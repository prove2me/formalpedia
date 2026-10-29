-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:24:48.089867+00:00
-- url     : https://prove2.me/theorems/f7754480-6b04-457b-945e-01aa7ce62c26
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / HelperCompleteness / Bracketed
-- statement:
--   This bundle develops the bracketed helper-completeness quantity used in the self-improvement proof. It reindexes helper mass into pointwise sandwich sums, identifies the named bracketed quantity, and derives the H-hat versus Z comparison and helper completeness from Cauchy-Schwarz, slackness, and consistency inputs.
--
--   Principal definitions:
--   - `helper_mass_eq_avg_pointwise_sandwich_sum`: reindexes the helper left-tensor mass.
--   - `sandwichedPolynomialOutcomeOperatorAt_sum_eq_bracketed`: the fiberwise operator reindexing identity.
--   - `helper_pointwise_sandwich_sum_eq_bracketed`: the pointwise bracketing identity.
--   - `helper_mass_eq_avg_pointwise_bracketed_sum`: the bracketed helper mass identity.
--   - `helperBracketedCompletenessQuantity_eq_mass`: identifies the named bracketed quantity with helper mass.
--   - `helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness`: derives the paper-shaped H-hat versus Z comparison.
--   - `helper_hhat_vs_z_of_self_consistency_and_complementary_slackness`: derives the comparison from point consistency.
--   - `helper_completeness_of_bracketed_cauchy_schwarz_input_consistency`: derives helper completeness from the bracketed inputs.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean#L32-L566

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
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
# Helper completeness: bracketed mass identities and reduced reductions

This file contains the exact bracketed reindexing of the helper-stage mass, the
paper-shaped completeness assemblies, and the reduced `addInU` reduction used
by the surrounding self-improvement theorem.

## References

- `references/ldt-paper/self_improvement.tex` lines 354--414
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

/-- Exact `Hhat` reindexing for the helper-stage left-tensor mass.

Expanding `Hhat = E_u H^u` through `subMeasMass ψ Hhat.liftLeft = ev ψ (Hhat.total ⊗ I)`,
swapping the leftTensor through the polynomial sum, and pulling the `ev` through
the per-outcome point average gives the paper identity

  `⟨ψ| Hhat ⊗ I |ψ⟩ = E_u Σ_h ⟨ψ| H^u_h ⊗ I |ψ⟩`,

where `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` is
`sandwichedPolynomialOutcomeOperatorAt`. This is the algebraic opening of the
helper-stage completeness chain at
`references/ldt-paper/self_improvement.tex`, lines 354--356, mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 103--106.

The conclusion is exact (not approximate) and depends on no input-consistency
or SDP hypotheses. The remaining helper-completeness ingredients --- the
Cauchy--Schwarz reductions
(`self_improvement.tex:360--403`) onto a `Z ⊗ I`-shaped expression, and the
input-consistency dual-mass bound already supplied by
`input_consistency_dual_mass_lower_bound` --- compose against this identity. -/
theorem helper_mass_eq_avg_pointwise_sandwich_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) := by
  -- Per-outcome scalar identity: `ev (leftTensor (Hhat.outcome h)) = E_u ev (leftTensor H^u_h)`.
  -- `Hhat.outcome h` is by definition the per-point average of
  -- `sandwichedPolynomialOutcomeOperatorAt`; pulling `ev (leftTensor _)` through
  -- the average is `ev_opTensor_averageOperatorOverDistribution_left` with `B = 1`.
  have hev_each :
      ∀ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome h)) =
          avgOver (uniformDistribution (Point params)) (fun u =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) := by
    intro h
    exact ev_opTensor_averageOperatorOverDistribution_left strategy.state
      (uniformDistribution (Point params))
      (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
      (1 : MIPStarRE.Quantum.Op ι)
  -- Open the LHS as a polynomial-indexed sum via the generic
  -- `ev_leftTensor_total_eq_sum_outcome`, replace each summand by its per-point
  -- average via `hev_each`, and swap sum/avgOver via `avgOver_sum`.
  calc
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft
        =
      ∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome h)) :=
        ev_leftTensor_total_eq_sum_outcome strategy.state _
    _ =
      ∑ h : Polynomial params,
        avgOver (uniformDistribution (Point params)) (fun u =>
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) :=
        Finset.sum_congr rfl (fun h _ => hev_each h)
    _ =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) := by
        rw [← avgOver_sum (uniformDistribution (Point params))
              (fun u h =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (sandwichedPolynomialOutcomeOperatorAt params strategy T u h)))]

/-- Operator-level fiberwise reindexing identity for the per-point sandwich
operator. Inside each fiber `{h : h u = a}` the inner `A^u_{h(u)}` is constant
(equal to `A^u_a`), and `Matrix.sum_mul`/`Matrix.mul_sum` pull this constant
factor through the sum over `T_h`. Mirrors the operator-level computation in
`sandwichedPolynomialSubMeasAt.total_le_one`. -/
private lemma sandwichedPolynomialOutcomeOperatorAt_sum_eq_bracketed
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    (∑ h : Polynomial params,
        sandwichedPolynomialOutcomeOperatorAt params strategy T u h) =
      ∑ a : Fq params,
        (strategy.pointMeasurement u).outcome a *
          (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
            T.outcome h) *
          (strategy.pointMeasurement u).outcome a := by
  classical
  rw [show (∑ h : Polynomial params,
              sandwichedPolynomialOutcomeOperatorAt params strategy T u h) =
            ∑ a : Fq params,
              ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                sandwichedPolynomialOutcomeOperatorAt params strategy T u h from by
          exact polynomial_sum_fiberwise params u
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u)]
  refine Finset.sum_congr rfl ?_
  intro a _
  have hreplace :
      ∀ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
        sandwichedPolynomialOutcomeOperatorAt params strategy T u h =
          (strategy.pointMeasurement u).outcome a *
            T.outcome h *
            (strategy.pointMeasurement u).outcome a := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    simp [sandwichedPolynomialOutcomeOperatorAt,
      pointConditionedOutcomeOperatorAtPolynomial, hh]
  rw [Finset.sum_congr rfl hreplace, ← Matrix.sum_mul, ← Matrix.mul_sum]

/-- Per-point bracketing identity for the helper-stage left-tensor mass.

Fiberwise reindexing by `h ↦ h(u)` and pulling `A^u_a · _ · A^u_a` through the
sum, `leftTensor`, and `ev` give the paper identity at a fixed point `u`:

  `Σ_h ⟨ψ| H^u_h ⊗ I |ψ⟩
    = Σ_a ⟨ψ| (A^u_a · T_{[h(u) = a]} · A^u_a) ⊗ I |ψ⟩`,

where `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` is
`sandwichedPolynomialOutcomeOperatorAt`, and the bracketed
`T_{[h(u) = a]} = Σ_{h : h u = a} T_h` is the inner fiber sum.

This is the identity `eq:bracketize-the-expression` of
`references/ldt-paper/self_improvement.tex`, lines 356--358 (mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 110--113), at a fixed
point `u` (before averaging). The conclusion is exact (not approximate) and
depends on no input-consistency, SDP, or self-consistency hypotheses; it is
purely an algebraic regrouping of `Σ_h H^u_h` by the value of `h` at `u`.

Composed with `helper_mass_eq_avg_pointwise_sandwich_sum`, this yields the
bracketed form `helper_mass_eq_avg_pointwise_bracketed_sum` of the helper-stage
`Hhat ⊗ I` mass, which is the starting point for the remaining
Cauchy--Schwarz reduction at `self_improvement.tex:360--403` toward
`eq:gonna-use-this-later-H-versus-Z`. -/
theorem helper_pointwise_sandwich_sum_eq_bracketed
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) =
      ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement u).outcome a *
              (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                T.outcome h) *
              (strategy.pointMeasurement u).outcome a)) := by
  classical
  calc
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u h)))
        =
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ h : Polynomial params,
            sandwichedPolynomialOutcomeOperatorAt params strategy T u h)) := by
        rw [← ev_finset_sum, leftTensor_finset_sum]
    _ =
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ a : Fq params,
            (strategy.pointMeasurement u).outcome a *
              (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                T.outcome h) *
              (strategy.pointMeasurement u).outcome a)) := by
        rw [sandwichedPolynomialOutcomeOperatorAt_sum_eq_bracketed]
    _ =
      ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement u).outcome a *
              (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                T.outcome h) *
              (strategy.pointMeasurement u).outcome a)) := by
        rw [← leftTensor_finset_sum, ev_finset_sum]

/-- Bracketed form of the helper-stage `Hhat ⊗ I` mass identity.

Combines `helper_mass_eq_avg_pointwise_sandwich_sum` with the per-point
bracketing identity `helper_pointwise_sandwich_sum_eq_bracketed`:

  `⟨ψ| Hhat ⊗ I |ψ⟩
    = E_u Σ_a ⟨ψ| (A^u_a · T_{[h(u) = a]} · A^u_a) ⊗ I |ψ⟩`,

where `T_{[h(u) = a]} = Σ_{h : h u = a} T_h`. This is the second equality in the
displayed completeness chain at
`references/ldt-paper/self_improvement.tex`, lines 354--358 (mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 103--113), composed
with the bracketing reindexing `eq:bracketize-the-expression`. The conclusion
is exact (not approximate) and depends on no input-consistency, SDP, or
self-consistency hypotheses. -/
theorem helper_mass_eq_avg_pointwise_bracketed_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              ((strategy.pointMeasurement u).outcome a *
                (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                  T.outcome h) *
                (strategy.pointMeasurement u).outcome a))) := by
  rw [helper_mass_eq_avg_pointwise_sandwich_sum]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  exact helper_pointwise_sandwich_sum_eq_bracketed params strategy T u

/-- The named bracketed helper-completeness quantity is exactly the
helper-stage `Hhat ⊗ I` mass for the averaged sandwiched family.

This is the Lean form of the equality labelled
`eq:bracketize-the-expression`, after composing the fiberwise reindexing with
the preceding expansion of `Hhat` as the average of the pointwise sandwiched
submeasurements. -/
theorem helperBracketedCompletenessQuantity_eq_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperBracketedCompletenessQuantity params strategy T =
      subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft := by
  rw [helper_mass_eq_avg_pointwise_bracketed_sum]
  rfl

/-- The paper-shaped `Hhat`-versus-`Z` comparison assembled from the bracketed
expression, the two Cauchy--Schwarz estimates, and complementary slackness.

The first Cauchy--Schwarz hypothesis moves from the bracketed expression
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a] A^u_a) ⊗ I ψ⟩` to
`helperFirstMovedCompletenessQuantity`.  The second removes the remaining
right-register copy of `A^u_a`, giving `helperLinearizedCompletenessQuantity`.
The latter is then identified with the dual mass by the SDP
complementary-slackness equation. -/
theorem helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
      subMeasMass strategy.state Hhat.liftLeft := by
  have hbracket_mass :
      helperBracketedCompletenessQuantity params strategy T.toSubMeas =
        subMeasMass strategy.state Hhat.liftLeft := by
    rw [hhelper.averagedConstruction]
    exact helperBracketedCompletenessQuantity_eq_mass params strategy T.toSubMeas
  refine
    helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper ?_ hremove_right hslack
  simpa [hbracket_mass] using hmove_left

/-- The `Hhat`-versus-`Z` comparison from point self-consistency and
complementary slackness.

This is the helper-completeness comparison at
`eq:gonna-use-this-later-H-versus-Z` with the two Cauchy--Schwarz estimates
supplied internally by `helper_first_move_abs_sub_bracketed_le_two_sqrt_delta`
and `helper_second_move_abs_sub_first_moved_le_sqrt_delta`. -/
theorem helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
      subMeasMass strategy.state Hhat.liftLeft :=
  helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
    params strategy eps delta hhelper
    (helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    (helper_second_move_abs_sub_first_moved_le_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    hslack

/-- Helper-stage completeness from the paper-shaped Cauchy--Schwarz estimates,
complementary slackness, and input consistency.

Compared with `helper_completeness_of_cauchy_schwarz_input_consistency`, this
version names the expression before the first Cauchy--Schwarz move exactly as
it appears in `eq:bracketize-the-expression`; the equality with the
`Hhat`-mass is supplied internally by
`helperBracketedCompletenessQuantity_eq_mass`. -/
theorem helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_input_consistency params strategy G eps delta nu
      heps hdelta hhelper ?_ hcons
  exact
    helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper hmove_left hremove_right hslack

/-- Helper-stage completeness from point self-consistency, complementary
slackness, and input consistency.

This theorem removes the two external Cauchy--Schwarz hypotheses from
`helper_completeness_of_bracketed_cauchy_schwarz_input_consistency`; both are
proved from the single point-measurement self-consistency hypothesis. -/
theorem helper_completeness_of_self_consistency_complementary_slackness_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
      params strategy G eps delta nu heps hdelta hhelper ?_ ?_ hslack hcons
  · exact helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
      params strategy T.toSubMeas delta hssc
  · exact helper_second_move_abs_sub_first_moved_le_sqrt_delta
      params strategy T.toSubMeas delta hssc

/-- Extract the orientation of complementary slackness used by the helper
completeness proof from the strengthened helper conclusion. -/
theorem helper_slackness_eq_of_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (h : Polynomial params) :
    T.toSubMeas.outcome h * averagedPointOperator params strategy h =
      T.toSubMeas.outcome h * Z :=
  (hhelper.complementarySlackness h).symm



/-- Helper-stage completeness from point self-consistency, a helper conclusion
carrying SDP complementary slackness, and input consistency.

This theorem removes the standalone `hslack` hypothesis from
`helper_completeness_of_self_consistency_complementary_slackness_input_consistency`;
the slackness equations are read from
`SelfImprovementHelperConclusionWithSlackness`. -/
theorem helper_completeness_of_self_consistency_helper_slackness_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_self_consistency_complementary_slackness_input_consistency
    params strategy G eps delta nu heps hdelta hhelper.toHelperConclusion hssc
    (helper_slackness_eq_of_helper_with_slackness params strategy eps delta hhelper)
    hcons

/-- Paper-origin statement for `lem:sdp` with complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 62--88 state
`\label{lem:sdp}` for the primal/dual SDP pair and assert optimal witnesses
`{T_g}`, `Z` with `∑ g, T_g = I` and `T_g Z = T_g A_g`.  Lines 168--190 prove
this by Slater strong duality and complementary slackness after passing through
the canonical SDP form.

The proof transports the formalized canonical optimal-pair output for the
Section 9 SDP back to the paper's abstract notation.  That canonical optimal
pair is obtained from the finite-dimensional strong-duality argument and the
slack-block saturation step in the matrix realization. -/
theorem sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    SdpStatementWithSlackness params strategy := by
  exact MatrixSdpStatementWithSlackness.toSdpStatementWithSlackness params strategy
    (matrixSdpPointRealization_statementWithSlackness params strategy)



-- The reduced add-in-u lemma invokes the global-variance transport record and
-- checks the full polynomial-indexed variance family.
/-- Reduced version of `lem:add-in-u`.

This currently keeps only the global-variance consequence used downstream. It
now derives that consequence from the post-triangle six-step edge-transport
chain bound via `globalVarianceOfPointsFromTransportChainBound`. The `gamma` and
`hgood` arguments are intentionally retained so this reduced theorem still
matches the surrounding self-improvement API and can be strengthened back to the
full paper statement without another caller-wide signature change. The
selection-dependent transfer inequality from the paper, together with its
dependence on an auxiliary family `M` and the averaged family `H`, is not yet
formalized here. -/
lemma addInU
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) ι) :
    AddInUStatement params strategy T eps delta := by
  refine
    { varianceBound := ?_ }
  let hglobalVariance :=
    globalVarianceOfPointsFromTransportChainBound params strategy eps delta gamma hgood
      T.toSubMeas
      (localVarianceTransportChainBound params strategy eps delta gamma hgood T.toSubMeas)
  simpa [selfImprovementVarianceError] using
    hglobalVariance.averagedGlobalVarianceBound
end MIPStarRE.LDT.SelfImprovement

end

end LIDT


