-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:15:45.345988+00:00
-- url     : https://prove2.me/theorems/ed8bf876-efbd-4043-a242-14ec9f1c4515
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / HelperCompleteness / Linearized
-- statement:
--   This bundle gives the linearized helper-completeness identities and the two comparison routes to a completeness lower bound.
--
--   Principal definitions:
--   - `helper_linearized_completeness_eq_dual_mass_of_complementary_slackness`: identifies the linearized quantity with dual mass.
--   - `helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness`: identifies the stored linearized quantity with dual mass.
--   - `helperBracketedCompletenessQuantity`: defines the bracketed comparison quantity.
--   - `helper_first_move_abs_sub_bracketed_le_two_sqrt_delta`: bounds the first comparison.
--   - `helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness`: bounds the second comparison.
--   - `helper_completeness_of_dual_mass_lower_bound`: derives completeness from a dual-mass bound.
--   - `helper_completeness_of_input_consistency`: derives completeness from input consistency.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Linearized.lean#L32-L448

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Linearized.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
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
# Helper completeness: the linearized SDP expression

This file rewrites the linearized helper-completeness expression as the dual
mass and assembles the Cauchy--Schwarz estimates with input consistency.  The
statements here are the algebraic bridge from the two analytic moves to the
`Hhat`-versus-`Z` lower bound.

## References

- `references/ldt-paper/self_improvement.tex` lines 395--414
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

/-- The final algebraic rewrite in the helper-completeness Cauchy--Schwarz
argument, isolated from the two analytic estimates.

After the two Cauchy--Schwarz moves in
`references/ldt-paper/self_improvement.tex`, lines 360--399, the remaining
linear expression is

`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩`.

This theorem reindexes the average to
`Σ_h ⟨ψ, (T_h E_u A^u_{h(u)}) ⊗ I ψ⟩`, applies the complementary-slackness
identity `T_h E_u A^u_{h(u)} = T_h Z`, and finally invokes
`sdp_complementary_slackness_sum_eq_dual_mass` to use `Σ_h T_h = I`.
The statement deliberately keeps complementary slackness as an explicit
hypothesis; it is not a consequence of the current reduced
`SdpOptimalPair` interface. -/
theorem helper_linearized_completeness_eq_dual_mass_of_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hTtotal : T.total = 1)
    (hslack :
      ∀ h : Polynomial params,
        T.outcome h * averagedPointOperator params strategy h =
          T.outcome h * Z) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) =
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  classical
  let 𝒟 := uniformDistribution (Point params)
  have hmul_avg :
      ∀ h : Polynomial params,
        averageOperatorOverDistribution 𝒟
            (fun u => T.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) =
          T.outcome h * averagedPointOperator params strategy h := by
    intro h
    calc
      averageOperatorOverDistribution 𝒟
          (fun u => T.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
          =
        ∑ u ∈ 𝒟.support,
          𝒟.weight u •
            (T.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) := by
          rfl
      _ =
        ∑ u ∈ 𝒟.support,
          T.outcome h *
            (𝒟.weight u •
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [mul_smul_comm]
      _ =
        T.outcome h *
          (∑ u ∈ 𝒟.support,
            𝒟.weight u •
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) := by
          rw [Matrix.mul_sum]
      _ =
        T.outcome h * averagedPointOperator params strategy h := by
          rfl
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))
        =
      ∑ h : Polynomial params,
        avgOver (uniformDistribution (Point params)) (fun u =>
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) := by
        rw [avgOver_sum]
    _ =
      ∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (T.outcome h * averagedPointOperator params strategy h)) := by
        refine Finset.sum_congr rfl ?_
        intro h _
        calc
          avgOver (uniformDistribution (Point params)) (fun u =>
              ev strategy.state
                (leftTensor (ι₂ := ι)
                  (T.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))
              =
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (averageOperatorOverDistribution 𝒟
                  (fun u =>
                    T.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) := by
              exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
                𝒟
                (fun u =>
                  T.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
                (1 : MIPStarRE.Quantum.Op ι)).symm
          _ =
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (T.outcome h * averagedPointOperator params strategy h)) := by
              rw [hmul_avg]
    _ = ev strategy.state (leftTensor (ι₂ := ι) Z) := by
        refine sdp_complementary_slackness_sum_eq_dual_mass
          params strategy T Z hTtotal ?_
        intro h
        exact (hslack h).symm

/-- The named linearized helper-completeness quantity is the SDP dual mass under
complementary slackness. -/
theorem helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hTtotal : T.total = 1)
    (hslack :
      ∀ h : Polynomial params,
        T.outcome h * averagedPointOperator params strategy h =
          T.outcome h * Z) :
    helperLinearizedCompletenessQuantity params strategy T =
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  simpa [helperLinearizedCompletenessQuantity] using
    helper_linearized_completeness_eq_dual_mass_of_complementary_slackness
      params strategy T Z hTtotal hslack



/-- The bracketed scalar expression before the first Cauchy--Schwarz move in
helper completeness.

This is the right-hand side of `eq:bracketize-the-expression`:

`E_u Σ_a ⟨ψ, (A^u_a · T_[h(u)=a] · A^u_a) ⊗ I ψ⟩`.

The finite sum
`Σ_{h : h(u)=a} T_h` represents the paper's fiber operator
`T_[h(u)=a]`. -/
noncomputable def helperBracketedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      ev strategy.state (leftTensor (ι₂ := ι) (Au * Tfiber * Au)))

/-- The first Cauchy--Schwarz move in the helper-completeness proof.

Assuming bipartite strong self-consistency of the point measurement with error
`delta`, the bracketed expression
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a] A^u_a) ⊗ I ψ⟩`
differs from
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩`
by at most `2 sqrt delta`.  The proof is the paper's
`eq:yet-another-move-a`: `twoNotionsOfSelfConsistency` supplies the first
square-root factor, while `helper_first_move_second_factor_le_one` supplies
the second. -/
theorem helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperFirstMovedCompletenessQuantity params strategy T -
      helperBracketedCompletenessQuantity params strategy T| ≤
      2 * Real.sqrt delta := by
  classical
  let Aop : Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a => leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a)
  let Bop : Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a => rightTensor (ι₁ := ι) ((strategy.pointMeasurement u).outcome a)
  let Cop : Point params → Fq params → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a _ =>
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Tfiber * Au)
  have hOutcome_herm : ∀ (u : Point params) (a : Fq params),
      ((strategy.pointMeasurement u).outcome a)ᴴ =
        (strategy.pointMeasurement u).outcome a := fun u a =>
    SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
  have hTfiber_herm : ∀ (u : Point params) (a : Fq params),
      (helperFiberOperator params T u a)ᴴ = helperFiberOperator params T u a := fun u a =>
    (Matrix.nonneg_iff_posSemidef.mp
      (helperFiberOperator_nonneg params T u a)).isHermitian.eq
  have hAop_herm : ∀ u a, (Aop u a)ᴴ = Aop u a := by
    intro u a
    simp [Aop, leftTensor_conjTranspose, hOutcome_herm u a]
  have hBop_herm : ∀ u a, (Bop u a)ᴴ = Bop u a := by
    intro u a
    simp [Bop, rightTensor_conjTranspose, hOutcome_herm u a]
  have hfun_A : ∀ u : Point params, (fun a : Fq params => (Aop u a)ᴴ) = Aop u := by
    intro u
    funext a
    exact hAop_herm u a
  have hfun_B : ∀ u : Point params, (fun a : Fq params => (Bop u a)ᴴ) = Bop u := by
    intro u
    funext a
    exact hBop_herm u a
  have hSDD := Preliminaries.twoNotionsOfSelfConsistency strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta
    ⟨strategy.permInvState, hssc⟩
  have hAB :
      avgOver (uniformDistribution (Point params)) (fun u =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop u a)ᴴ)
          (fun a : Fq params => (Bop u a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro u
    rw [hfun_A u, hfun_B u]
    rfl
  have hC : ∀ u : Point params,
      (∑ a : Fq params, (∑ b : Unit, Cop u a b)ᴴ * (∑ b : Unit, Cop u a b)) ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    intro u
    have hop := helper_first_move_second_factor_operator_le_one params strategy T u
    simpa [Cop, leftTensor_conjTranspose, leftTensor_mul_leftTensor, Matrix.conjTranspose_mul,
      hOutcome_herm, hTfiber_herm, mul_assoc] using hop
  have hcs := Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params))
    (uniformDistribution_weight_sum_le_one (Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hbracket :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Aop u a * Cop u a b)) =
        helperBracketedCompletenessQuantity params strategy T := by
    unfold helperBracketedCompletenessQuantity
    refine avgOver_congr _ _ _ ?_
    intro u
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [Aop, Cop, leftTensor_mul_leftTensor, mul_assoc]
  have hfirst :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Bop u a * Cop u a b)) =
        helperFirstMovedCompletenessQuantity params strategy T := by
    unfold helperFirstMovedCompletenessQuantity
    refine avgOver_congr _ _ _ ?_
    intro u
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [Bop, Cop, rightTensor_mul_leftTensor_eq_opTensor]
  have hsqrt2_le_2 : Real.sqrt 2 ≤ (2 : Error) := by
    nlinarith [Real.mul_self_sqrt (by norm_num : (0 : Error) ≤ 2),
      Real.sqrt_nonneg (2 : Error)]
  have hsqrt2delta_le :
      Real.sqrt (2 * delta) ≤ 2 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : Error) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrt2_le_2 (Real.sqrt_nonneg _)
  calc
    |helperFirstMovedCompletenessQuantity params strategy T -
      helperBracketedCompletenessQuantity params strategy T|
        = |avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Aop u a * Cop u a b)) -
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Bop u a * Cop u a b))| := by
          rw [hbracket, hfirst]
          exact abs_sub_comm _ _
    _ ≤ Real.sqrt (2 * delta) := hcs
    _ ≤ 2 * Real.sqrt delta := hsqrt2delta_le

/-- The recorded `Hhat`-versus-`Z` comparison follows from the two
Cauchy--Schwarz scalar bounds and complementary slackness.

The first hypothesis is the bound for moving the leftmost copy of `A^u_a` across
the bipartition; the second is the bound for removing the remaining copy of
`A^u_a` on the right register.  Together with complementary slackness, these
are precisely the estimates leading to
`eq:gonna-use-this-later-H-versus-Z` in the paper. -/
theorem helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
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
        subMeasMass strategy.state Hhat.liftLeft| ≤
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
  have hmove_left_upper :
      helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        subMeasMass strategy.state Hhat.liftLeft ≤
        2 * Real.sqrt delta :=
    (abs_le.mp hmove_left).2
  have hremove_right_upper :
      helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas ≤
        Real.sqrt delta :=
    (abs_le.mp hremove_right).2
  have hlinearized :
      helperLinearizedCompletenessQuantity params strategy T.toSubMeas =
        ev strategy.state (leftTensor (ι₂ := ι) Z) :=
    helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness
      params strategy T.toSubMeas Z hhelper.sdpWitness.primalTotalOperator hslack
  linarith

/-- Helper-stage completeness from the `Hhat`-versus-`Z` comparison and the
dual-mass lower bound.

The paper proves
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ` by the two
Cauchy--Schwarz moves in the helper-completeness paragraph.  Once the separate
input-consistency argument gives `1 - ν ≤ ⟨ψ, Z ⊗ I, ψ⟩`, this theorem performs
the scalar assembly and absorbs the loss `3 √δ` into the helper threshold
`ζ̂ = selfImprovementHelperError params eps delta`. -/
theorem helper_completeness_of_dual_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hHhat_vs_Z :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft)
    (hdualMass :
      1 - nu ≤ ev strategy.state (leftTensor (ι₂ := ι) Z)) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  have herr :=
    helper_completeness_error_le_selfImprovementHelperError params eps delta heps hdelta
  linarith

/-- Helper-stage completeness from input consistency and the
`Hhat`-versus-`Z` comparison.

This is the checked assembly of the final part of the helper-completeness
paragraph in `thm:self-improvement`.  The only analytic input still external is
the paper's Cauchy--Schwarz comparison
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ`; the SDP dual-feasibility
fields of `SelfImprovementHelperConclusion` and the input consistency of `G`
produce the dual-mass lower bound internally. -/
theorem helper_completeness_of_input_consistency
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
    (hHhat_vs_Z :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_dual_mass_lower_bound params strategy eps delta nu
      heps hdelta hHhat_vs_Z ?_
  exact
    input_consistency_dual_mass_lower_bound params strategy G Z nu
      hhelper.sdpWitness.dualPositive hhelper.sdpWitness.dualFeasible hcons


end MIPStarRE.LDT.SelfImprovement

end

end LIDT


