-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:09:42.260781+00:00
-- url     : https://prove2.me/theorems/688514c2-b238-4ad7-8f32-a6438c8abae2
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / HelperCompleteness / FiberBounds
-- statement:
--   This bundle defines the fiber operators and scalar quantities used in the helper-completeness Cauchy-Schwarz argument. It proves positivity, identity domination, and total decomposition of fibers, then records the first moved completeness quantities and their operator bounds.
--
--   Principal definitions:
--   - `helperFiberOperator`: the helper fiber operator for a pointwise polynomial value.
--   - `helperFiberOperator_nonneg`: positivity of the helper fiber operator.
--   - `helperFiberOperator_le_one`: domination of the helper fiber operator by identity.
--   - `helperFiberOperator_sum_eq_total`: the fiber sum equals the total SDP submeasurement operator.
--   - `helper_second_move_first_factor_operator_le_one`: the pointwise first-factor operator bound.
--   - `helper_second_move_first_factor_le_one`: the corresponding scalar bound.
--   - `helperFirstMovedCompletenessQuantity`: the quantity after the first Cauchy-Schwarz move.
--   - `helperLinearizedCompletenessQuantity`: the quantity after removing the remaining point operator.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/FiberBounds.lean#L35-L590

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/FiberBounds.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Helper completeness: fiber operators and Cauchy--Schwarz bounds

This file introduces the fiber operator `T_[h(u)=a]` and proves the pointwise
operator inequalities and averaged Cauchy--Schwarz estimates used in the two
analytic moves of the helper-completeness proof.

## References

- `references/ldt-paper/self_improvement.tex` lines 359--394
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

/-- The fiber operator `T_[h(u)=a]` in the helper-completeness proof.

It is the sum of all SDP-measurement outcomes indexed by polynomials whose
value at the point `u` is `a`. -/
noncomputable def helperFiberOperator
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) : MIPStarRE.Quantum.Op ι :=
  ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a), T.outcome h

/-- The helper fiber operator is positive. -/
theorem helperFiberOperator_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    0 ≤ helperFiberOperator params T u a :=
  Finset.sum_nonneg fun h _ => T.outcome_pos h

/-- The helper fiber operator is bounded by the identity. -/
theorem helperFiberOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    helperFiberOperator params T u a ≤ 1 := by
  calc
    helperFiberOperator params T u a
        ≤ ∑ h : Polynomial params, T.outcome h :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun h _ _ => T.outcome_pos h)
    _ = T.total := T.sum_eq_total
    _ ≤ 1 := T.total_le_one

/-- The fiber operators over all values at a fixed point sum to the total SDP
submeasurement operator. -/
theorem helperFiberOperator_sum_eq_total
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params, helperFiberOperator params T u a) = T.total := by
  calc
    (∑ a : Fq params, helperFiberOperator params T u a)
        = ∑ h : Polynomial params, T.outcome h := by
          simpa [helperFiberOperator] using (polynomial_sum_fiberwise params u T.outcome).symm
    _ = T.total := T.sum_eq_total

/-- Pointwise operator form of the identity bound for the first
Cauchy--Schwarz factor in the second helper-completeness move.

At a fixed point `u`, the fiber operators form a submeasurement after grouping
by the value `h(u)`.  Thus `Σ_a T_[h(u)=a]^2 ≤ Σ_a T_[h(u)=a] = T.total ≤ I`. -/
theorem helper_second_move_first_factor_operator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params,
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Tfiber * Tfiber)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  calc
    (∑ a : Fq params,
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Tfiber * Tfiber))
        ≤ ∑ a : Fq params, leftTensor (ι₂ := ι)
          (helperFiberOperator params T u a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          have hT_nonneg : 0 ≤ helperFiberOperator params T u a :=
            helperFiberOperator_nonneg params T u a
          have hT_le_one : helperFiberOperator params T u a ≤ 1 :=
            helperFiberOperator_le_one params T u a
          have hT_sq_le : helperFiberOperator params T u a *
              helperFiberOperator params T u a ≤ helperFiberOperator params T u a :=
            MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one
          simpa [leftTensor, opTensor] using
            (opTensor_mono_left (ι₂ := ι)
              (B := (1 : MIPStarRE.Quantum.Op ι)) hT_sq_le
              (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1))
    _ = leftTensor (ι₂ := ι) (∑ a : Fq params, helperFiberOperator params T u a) := by
        rw [leftTensor_finset_sum]
    _ = leftTensor (ι₂ := ι) T.total := by
        rw [helperFiberOperator_sum_eq_total]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) T.total_le_one

/-- The first Cauchy--Schwarz factor in the second helper-completeness move is
bounded by one.

This is the Lean form of the paper's assertion, following
`eq:mysterious-case-of-the-disappearing-a`, that
`E_u Σ_a ⟨ψ, T_[h(u)=a]^2 ⊗ I ψ⟩ ≤ 1`. -/
theorem helper_second_move_first_factor_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Tfiber := helperFiberOperator params T u a
        ev strategy.state (leftTensor (ι₂ := ι) (Tfiber * Tfiber))) ≤
      1 := by
  refine Distribution.IsProbability.avgOver_le_of_forall_le_on_support
    (𝒟 := uniformDistribution (Point params))
    (uniformDistribution_isProbability (Point params)) _ 1 ?_
  intro u _
  have hop := helper_second_move_first_factor_operator_le_one params T u
  have hev := ev_mono strategy.state _ _ hop
  rw [ev_sum] at hev
  simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using hev

/-- Pointwise comparison between the projective residual in the second
Cauchy--Schwarz move and the bipartite strong self-consistency defect.

Projectivity gives `(A^u_a)^2 = A^u_a` and `(I - A^u_a)^2 = I - A^u_a`.
After summing over `a`, the residual is the one-register total mass minus the
diagonal cross-register overlap, and hence is bounded by the `max 0` defining
`qBipartiteSSCDefect`. -/
theorem helper_second_move_second_factor_pointwise_le_qBipartiteSSCDefect
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (u : Point params) :
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))) ≤
      qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas) := by
  classical
  have hresidual_eq :
      (∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))) =
        ev strategy.state
          (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).toSubMeas.total)) -
          ∑ a : Fq params,
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a)) := by
    calc
      (∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au))))
          =
        ∑ a : Fq params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (1 - (strategy.pointMeasurement u).outcome a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            set Au := (strategy.pointMeasurement u).outcome a
            have hproj : Au * Au = Au := by
              simpa [Au] using (strategy.pointMeasurement u).proj a
            have hsq : (1 - Au) * (1 - Au) = 1 - Au := by
              calc
                (1 - Au) * (1 - Au) = 1 - Au - Au + Au * Au := by noncomm_ring
                _ = 1 - Au := by rw [hproj]; noncomm_ring
            simp [Au, hproj, hsq]
      _ =
        ∑ a : Fq params,
          (ev strategy.state (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a)) -
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [← ev_sub]
            congr 1
            simpa [leftTensor, opTensor] using
              (MIPStarRE.Quantum.kronecker_sub_right
                (A := (strategy.pointMeasurement u).outcome a)
                (B₁ := (1 : MIPStarRE.Quantum.Op ι))
                (B₂ := (strategy.pointMeasurement u).outcome a)).symm
      _ =
        (∑ a : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a))) -
          ∑ a : Fq params,
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a)) := by
            rw [Finset.sum_sub_distrib]
      _ =
        ev strategy.state
          (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).toSubMeas.total)) -
          ∑ a : Fq params,
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a)) := by
            rw [← ev_sum strategy.state
              (fun a : Fq params =>
                leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a))]
            rw [leftTensor_finset_sum, (strategy.pointMeasurement u).toSubMeas.sum_eq_total]
  rw [hresidual_eq]
  unfold qBipartiteSSCDefect
  exact le_max_right 0 _

/-- The second Cauchy--Schwarz factor in the second helper-completeness move is
bounded by the bipartite strong self-consistency error.

This is the Lean form of the paper's assertion that
`E_u Σ_a ⟨ψ, A^u_a ⊗ (I-A^u_a) ψ⟩ ≤ delta`. -/
theorem helper_second_move_second_factor_le_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))) ≤
      delta := by
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au))))
        ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas)) := by
        refine avgOver_mono _ _ _ ?_
        intro u
        exact helper_second_move_second_factor_pointwise_le_qBipartiteSSCDefect
          params strategy u
    _ ≤ delta := hssc.overlapBound

/-- Pointwise operator form of the identity bound for the second
Cauchy--Schwarz factor in the first helper-completeness move.

For a fixed point `u`, each fiber operator satisfies
`0 ≤ T_[h(u)=a] ≤ I`, hence `T_[h(u)=a]^2 ≤ I`.  Sandwiching by the
projection `A^u_a` gives
`A^u_a T_[h(u)=a]^2 A^u_a ≤ A^u_a`, and the projective measurement
`A^u` sums to the identity. -/
theorem helper_first_move_second_factor_operator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Au * (Tfiber * Tfiber) * Au)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  have hsum :
      (∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        let Tfiber := helperFiberOperator params T u a
        leftTensor (ι₂ := ι) (Au * (Tfiber * Tfiber) * Au)) ≤
        ∑ a : Fq params, leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement u).outcome a) := by
    refine Finset.sum_le_sum ?_
    intro a _
    set Au := (strategy.pointMeasurement u).outcome a
    set Tfiber := helperFiberOperator params T u a
    have hT_nonneg : 0 ≤ Tfiber := by
      simpa [Tfiber] using helperFiberOperator_nonneg params T u a
    have hT_le_one : Tfiber ≤ 1 := by
      simpa [Tfiber] using helperFiberOperator_le_one params T u a
    have hT_sq_le_one : Tfiber * Tfiber ≤ 1 := by
      exact le_trans (MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one) hT_le_one
    have hAu_herm : Auᴴ = Au := by
      simpa [Au] using
        SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
    have hAu_proj : Au * Au = Au := by
      simpa [Au] using (strategy.pointMeasurement u).proj a
    have hterm : Au * (Tfiber * Tfiber) * Au ≤ Au := by
      calc
        Au * (Tfiber * Tfiber) * Au
            ≤ Au * 1 * Au :=
              IsSelfAdjoint.conjugate_le_conjugate hT_sq_le_one hAu_herm
        _ = Au := by simp [hAu_proj]
    simpa [leftTensor, opTensor] using
      (opTensor_mono_left (ι₂ := ι)
        (B := (1 : MIPStarRE.Quantum.Op ι)) hterm
        (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1))
  calc
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Au * (Tfiber * Tfiber) * Au))
        ≤ ∑ a : Fq params, leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement u).outcome a) := hsum
    _ = leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).toSubMeas.total) := by
        rw [leftTensor_finset_sum, (strategy.pointMeasurement u).toSubMeas.sum_eq_total]
    _ = 1 := by
        rw [(strategy.pointMeasurement u).total_eq_one, leftTensor_one]



/-- The scalar expression after the first Cauchy--Schwarz move in helper
completeness.

This is
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩`, the right-hand side of
`eq:yet-another-move-a` in the paper.  The fiber
`T_[h(u)=a]` is represented by the finite sum over polynomials whose value at
`u` is `a`. -/
noncomputable def helperFirstMovedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      ev strategy.state (opTensor (Tfiber * Au) Au))

/-- The scalar expression after removing the remaining point-measurement
operator in helper completeness.

This is
`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩`.  Complementary slackness identifies this
quantity with the dual mass `⟨ψ, Z ⊗ I ψ⟩`. -/
noncomputable def helperLinearizedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (T.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))

/-- Fiberwise form of the linearized helper-completeness quantity.

The expression
`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩` may equivalently be grouped by the value
`a = h(u)`, giving
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ I ψ⟩`.  This is the algebraic rewrite used
after `eq:mysterious-case-of-the-disappearing-a` in the paper. -/
theorem helper_linearized_completeness_quantity_eq_fiber_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperLinearizedCompletenessQuantity params strategy T =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          let Au := (strategy.pointMeasurement u).outcome a
          let Tfiber := helperFiberOperator params T u a
          ev strategy.state (leftTensor (ι₂ := ι) (Tfiber * Au))) := by
  unfold helperLinearizedCompletenessQuantity
  refine avgOver_congr _ _ _ ?_
  intro u
  rw [show (∑ h : Polynomial params,
      ev strategy.state (leftTensor (ι₂ := ι)
        (T.outcome h * pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) =
      ∑ a : Fq params, ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
        ev strategy.state (leftTensor (ι₂ := ι)
          (T.outcome h * pointConditionedOutcomeOperatorAtPolynomial params strategy h u)) from by
      exact polynomial_sum_fiberwise params u
        (fun h => ev strategy.state (leftTensor (ι₂ := ι)
          (T.outcome h * pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [← ev_finset_sum]
  congr 1
  rw [leftTensor_finset_sum]
  congr 1
  calc
    (∑ x ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
      T.outcome x * pointConditionedOutcomeOperatorAtPolynomial params strategy x u)
        = ∑ x ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
            T.outcome x * (strategy.pointMeasurement u).outcome a := by
          refine Finset.sum_congr rfl ?_
          intro h hh
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
          simp [pointConditionedOutcomeOperatorAtPolynomial, hh]
    _ = (∑ x ∈ Finset.univ.filter (fun h : Polynomial params => h u = a), T.outcome x) *
          (strategy.pointMeasurement u).outcome a := by
          rw [Finset.sum_mul]

/-- Pointwise Cauchy--Schwarz estimate for the second helper-completeness move.

For fixed `u` and `a`, this bounds the residual term
`⟨ψ, (T_[h(u)=a] A^u_a) ⊗ (I - A^u_a) ψ⟩` by the product of the two square-root
factors appearing after `eq:mysterious-case-of-the-disappearing-a`. -/
theorem helper_second_move_pointwise_abs_le_sqrt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    |ev strategy.state (opTensor
      (helperFiberOperator params T u a * (strategy.pointMeasurement u).outcome a)
      (1 - (strategy.pointMeasurement u).outcome a))| ≤
      Real.sqrt (ev strategy.state (leftTensor (ι₂ := ι)
        (helperFiberOperator params T u a * helperFiberOperator params T u a))) *
      Real.sqrt (ev strategy.state (opTensor
        ((strategy.pointMeasurement u).outcome a * (strategy.pointMeasurement u).outcome a)
        ((1 - (strategy.pointMeasurement u).outcome a) *
          (1 - (strategy.pointMeasurement u).outcome a)))) := by
  set Tf := helperFiberOperator params T u a
  set Au := (strategy.pointMeasurement u).outcome a
  have hTf_herm : Tfᴴ = Tf := by
    simpa [Tf] using (Matrix.nonneg_iff_posSemidef.mp
      (helperFiberOperator_nonneg params T u a)).isHermitian.eq
  have hAu_herm : Auᴴ = Au := by
    simpa [Au] using SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
  have hOneSub_herm : (1 - Au)ᴴ = 1 - Au := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hAu_herm]
  have hcs := ev_abs_mul_le_sqrt strategy.state
    (leftTensor (ι₂ := ι) Tf)
    (opTensor Au (1 - Au))
  change |ev strategy.state (opTensor Tf (1 : MIPStarRE.Quantum.Op ι) *
      opTensor Au (1 - Au))| ≤
    Real.sqrt (ev strategy.state
      (opTensor Tf (1 : MIPStarRE.Quantum.Op ι) *
        (opTensor Tf (1 : MIPStarRE.Quantum.Op ι))ᴴ)) *
    Real.sqrt (ev strategy.state
      ((opTensor Au (1 - Au))ᴴ * opTensor Au (1 - Au))) at hcs
  rw [opTensor_mul] at hcs
  rw [conjTranspose_opTensor, hTf_herm, Matrix.conjTranspose_one, opTensor_mul] at hcs
  rw [conjTranspose_opTensor, hAu_herm, hOneSub_herm, opTensor_mul] at hcs
  simpa [Tf, Au, leftTensor, opTensor] using hcs

/-- The second Cauchy--Schwarz move in the helper-completeness proof.

Assuming bipartite strong self-consistency of the point measurement with error
`delta`, the first-moved helper-completeness expression
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩` differs from the linearized
expression `E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ I ψ⟩` by at most `sqrt delta`.
The first factor is bounded by the grouped submeasurement estimate, and the
second is exactly the projective residual controlled by self-consistency. -/
theorem helper_second_move_abs_sub_first_moved_le_sqrt_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperLinearizedCompletenessQuantity params strategy T -
      helperFirstMovedCompletenessQuantity params strategy T| ≤
      Real.sqrt delta := by
  classical
  let t : Point params → Fq params → Error := fun u a =>
    let Au := (strategy.pointMeasurement u).outcome a
    let Tfiber := helperFiberOperator params T u a
    ev strategy.state (opTensor (Tfiber * Au) (1 - Au))
  let x : Point params → Fq params → Error := fun u a =>
    let Tfiber := helperFiberOperator params T u a
    ev strategy.state (leftTensor (ι₂ := ι) (Tfiber * Tfiber))
  let y : Point params → Fq params → Error := fun u a =>
    let Au := (strategy.pointMeasurement u).outcome a
    ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))
  have ht : ∀ u a, |t u a| ≤ Real.sqrt (x u a) * Real.sqrt (y u a) := by
    intro u a
    exact helper_second_move_pointwise_abs_le_sqrt params strategy T u a
  have hx : ∀ u a, 0 ≤ x u a := by
    intro u a
    set Tf := helperFiberOperator params T u a
    have hTf_herm : Tfᴴ = Tf := by
      simpa [Tf] using (Matrix.nonneg_iff_posSemidef.mp
        (helperFiberOperator_nonneg params T u a)).isHermitian.eq
    have hnonneg := ev_adjoint_self_nonneg strategy.state (leftTensor (ι₂ := ι) Tf)
    simpa [x, Tf, leftTensor_conjTranspose, hTf_herm, leftTensor_mul_leftTensor] using hnonneg
  have hy : ∀ u a, 0 ≤ y u a := by
    intro u a
    set Au := (strategy.pointMeasurement u).outcome a
    have hAu_herm : Auᴴ = Au := by
      simpa [Au] using SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
    have hOneSub_herm : (1 - Au)ᴴ = 1 - Au := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hAu_herm]
    have hnonneg := ev_adjoint_self_nonneg strategy.state (opTensor Au (1 - Au))
    simpa [y, Au, conjTranspose_opTensor, hAu_herm, hOneSub_herm, opTensor_mul] using hnonneg
  have hweighted := MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
    (Question := Point params) (Outcome := Fq params)
    (uniformDistribution (Point params)) t x y ht hx hy
  have hgap :
      avgOver (uniformDistribution (Point params)) (fun u => ∑ a : Fq params, t u a) =
        helperLinearizedCompletenessQuantity params strategy T -
          helperFirstMovedCompletenessQuantity params strategy T := by
    rw [helper_linearized_completeness_quantity_eq_fiber_sum]
    unfold helperFirstMovedCompletenessQuantity
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro u
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    dsimp [t]
    set Au := (strategy.pointMeasurement u).outcome a
    set Tfiber := helperFiberOperator params T u a
    rw [← ev_sub]
    congr 1
    simpa [leftTensor, opTensor, Tfiber, Au] using
      (MIPStarRE.Quantum.kronecker_sub_right
        (A := Tfiber * Au) (B₁ := (1 : MIPStarRE.Quantum.Op ι)) (B₂ := Au)).symm
  have hx_avg_le_one :
      avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, x u a) ≤
        1 := by
    simpa [x] using helper_second_move_first_factor_le_one params strategy T
  have hy_avg_le_delta :
      avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, y u a) ≤
        delta := by
    simpa [y] using helper_second_move_second_factor_le_delta params strategy delta hssc
  have hsqrt_x_le_one :
      Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, x u a)) ≤
        1 := by
    simpa using Real.sqrt_le_sqrt hx_avg_le_one
  have hsqrt_y_le_delta :
      Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, y u a)) ≤
        Real.sqrt delta :=
    Real.sqrt_le_sqrt hy_avg_le_delta
  calc
    |helperLinearizedCompletenessQuantity params strategy T -
      helperFirstMovedCompletenessQuantity params strategy T|
        = |avgOver (uniformDistribution (Point params))
            (fun u => ∑ a : Fq params, t u a)| := by
          rw [hgap]
    _ ≤ Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, x u a)) *
        Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, y u a)) :=
          hweighted
    _ ≤ 1 * Real.sqrt delta := by
        exact mul_le_mul hsqrt_x_le_one hsqrt_y_le_delta
          (Real.sqrt_nonneg _) (by norm_num : (0 : Error) ≤ 1)
    _ = Real.sqrt delta := by ring
end MIPStarRE.LDT.SelfImprovement

end

end LIDT


