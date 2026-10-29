-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:18:29.012616+00:00
-- url     : https://prove2.me/theorems/c841f266-6bee-4fe2-b707-472ea46b7aca
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUStep12 / Raw
-- statement:
--   This bundle records the raw Cauchy-Schwarz estimates for the first two add-in-u chain moves. It supplies the contraction side conditions and the resulting square-root bounds for the differences between successive scalar quantities.
--
--   Principal definitions:
--   - `addInU_step1_C_contraction`: the contraction side condition for Step 1.
--   - `addInU_cs_chain_step1_abs_le_sqrt_two_delta`: the raw square-root bound for Q0 minus Q1.
--   - `addInU_step2_C_contraction`: the contraction side condition for Step 2.
--   - `addInU_cs_chain_step2_abs_le_sqrt_two_delta`: the raw square-root bound for Q1 minus Q2.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Raw.lean#L42-L648

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Raw.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Unselected add-in-u Step 1/2 Cauchy--Schwarz bounds

Unselected-family contraction inputs and raw `√(2δ)` estimates for the first
two add-in-u moves in the self-improvement chain.
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Raw Cauchy--Schwarz bound for the add-in-u Step 1 difference

This section proves the raw `|Q₀ - Q₁| ≤ √(2δ)` bound from
`references/ldt-paper/self_improvement.tex`, lines 255--277 (`eq:move-one`).

The proof combines:
* `addInU_cs_chain_step1_diff_eq` (algebraic alignment to commutator-times-PSD),
* `addInU_pointMeasurement_snd_selfConsistency` (`A^v` self-consistency lifted
  to the `(u, v)` average),
* `addInU_filtered_sandwiched_tensor_sum_le_one` (filtered sandwich-tensor mass
  is a contraction),
* `Preliminaries.closenessOfInnerProduct_right` (the weighted Cauchy--Schwarz
  inner-product bound from `prop:closeness-of-ip`, `eq:closeness4`).

The analogous Step 2 bound (`|Q₁ - Q₂| ≤ √(2δ)`) is proved by the same
strategy with `closenessOfInnerProduct_left` and the `leftTensor`-sandwiched
analogue of the Step 1 contraction lemma. -/

/-- Cauchy--Schwarz contraction side condition for Step 1.

For a fixed `(u, v)`, the right-tensor-sandwiched sum
`Σ_a (rightTensor A^v_a · K_{u,v,a})ᴴ · (rightTensor A^v_a · K_{u,v,a}) ≤ 1`
where `K_{u,v,a} = Σ_{h: h(v)=a} (M^u_h ⊗ T_h)`.  This is the C side condition
fed to `closenessOfInnerProduct_right` in the Step 1 raw bound proof. -/
private lemma addInU_step1_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0))ᴴ *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  -- Notation: K(a) is the filtered sandwich-tensor mass at fiber `h v = a`,
  -- and Pa is the right-placed point projection `I ⊗ A^v_a`.
  set K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
      opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
        (T.outcome h)
  set Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    rightTensor (ι₁ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  -- Step (a): rewrite each indexed `Σ_h …` as `K a * Pa a`
  have hsum_eq : ∀ a : Fq params,
      (∑ h : Polynomial params,
          (if h uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h) *
              rightTensor (ι₁ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
          else 0)) = K a * Pa a := by
    intro a
    have hfilter :
        (∑ h : Polynomial params,
          (if h uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h) *
              rightTensor (ι₁ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
          else 0)) =
            ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) := by
      rw [Finset.sum_filter]
    rw [hfilter, ← Finset.sum_mul]
  -- Step (b): K a is Hermitian (sum of Hermitian summands)
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hMh_herm : ∀ h : Polynomial params,
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)ᴴ =
          (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)).isHermitian.eq
    have hTh_herm : ∀ h : Polynomial params,
        (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hMh_herm, hTh_herm]
  -- Step (c): Pa a is Hermitian (rightTensor of a Hermitian projection)
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, rightTensor_conjTranspose, hOutcome_herm]
  -- Step (d): Pa a is a projection (Pa a * Pa a = Pa a)
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_mul_rightTensor, hproj]
  -- Step (e): K a is PSD and ≤ 1
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro h _
    exact opTensor_nonneg
      ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)
      (T.outcome_pos h)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_filtered_sandwiched_tensor_sum_le_one params strategy T uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  -- Step (f): bound each summand `(K a * Pa a)ᴴ * (K a * Pa a) ≤ Pa a`
  have hterm_le : ∀ a : Fq params,
      (K a * Pa a)ᴴ * (K a * Pa a) ≤ Pa a := by
    intro a
    -- Expand: (K · Pa)ᴴ · (K · Pa) = Pa · K² · Pa
    have hexpand : (K a * Pa a)ᴴ * (K a * Pa a) = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := IsSelfAdjoint.conjugate_le_conjugate (hK_sq_le_one a) (hPa_herm a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  -- Step (g): sum the pointwise bounds and use `Σ_a Pa a = 1`
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [rightTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, rightTensor_one]
  -- Step (h): conclude
  calc
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0))ᴴ *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
            else 0))
        = ∑ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Raw `|Q₀ - Q₁| ≤ √(2δ)` bound for the add-in-u Step 1 Cauchy--Schwarz move.

Proves the paper's `eq:move-one` bound from
`references/ldt-paper/self_improvement.tex`, lines 255--277, as a completed
construction.  The proof combines the algebraic alignment
`addInU_cs_chain_step1_diff_eq` with the weighted Cauchy--Schwarz inner-product
bound `Preliminaries.closenessOfInnerProduct_right`, the `A^v` self-consistency
input via `addInU_pointMeasurement_snd_selfConsistency`, and the
filtered-tensor contraction `addInU_filtered_sandwiched_tensor_sum_le_one`.

The hypothesis is the bipartite SSC for the unlifted point measurement on the
single-point distribution; the lifted `2δ` bound is constructed inside the
proof via `addInU_pointMeasurement_snd_selfConsistency`. -/
lemma addInU_cs_chain_step1_abs_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
      Real.sqrt (2 * delta) := by
  classical
  -- Self-consistency input: SDD ≤ 2δ between left/right point-measurement lifts
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  -- Operator families for closenessOfInnerProduct_right
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a h =>
      if h uv.2 = a then
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
      else 0
  -- Hermitian-ness of A and B (from projection outcomes of pointMeasurement)
  have hOutcome_herm : ∀ (v : Point params) (a : Fq params),
      ((strategy.pointMeasurement v).toSubMeas.outcome a)ᴴ =
        (strategy.pointMeasurement v).toSubMeas.outcome a := fun v a =>
    (Matrix.nonneg_iff_posSemidef.mp
      ((strategy.pointMeasurement v).toSubMeas.outcome_pos a)).isHermitian.eq
  have hAop_herm : ∀ uv a, (Aop uv a)ᴴ = Aop uv a := by
    intro uv a
    change (leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hBop_herm : ∀ uv a, (Bop uv a)ᴴ = Bop uv a := by
    intro uv a
    change (rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_conjTranspose, hOutcome_herm uv.2 a]
  -- Match qSDDCore on Hermitian-conjugates with qSDDCore directly
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
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop uv a)ᴴ) (fun a : Fq params => (Bop uv a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hfun_A uv, hfun_B uv]
    rfl
  -- The C contraction side condition
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ h : Polynomial params, Cop uv a h)ᴴ *
            (∑ h : Polynomial params, Cop uv a h)) ≤ 1 :=
    fun uv => addInU_step1_C_contraction params strategy T uv
  -- Apply `closenessOfInnerProduct_right`
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  -- Match `Σ_a Σ_h ev(A · C - B · C)` to `addInUCSChainQ1 - addInUCSChainQ0`
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a h)) -
        (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a h)) =
      ∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
            (opTensor Mh (T.outcome h) * rightTensor (ι₁ := ι) Av)) := by
    intro uv
    -- Convert each `Σ_a Σ_h …` into a single `Σ_h …` via the fiber filter
    have hAvg : ∀ (X : Fq params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι)),
        (∀ a h, h uv.2 ≠ a → X a h = 0) →
        ∑ a : Fq params, ∑ h : Polynomial params, ev strategy.state (X a h) =
          ∑ h : Polynomial params, ev strategy.state (X (h uv.2) h) := by
      intro X hX
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro h _
      have hsingle : ∑ a : Fq params, ev strategy.state (X a h) =
          ev strategy.state (X (h uv.2) h) := by
        rw [Finset.sum_eq_single (h uv.2)]
        · intro a _ ha
          rw [hX a h (Ne.symm ha), ev_zero strategy.state]
        · intro hmem
          exact (hmem (Finset.mem_univ _)).elim
      exact hsingle
    have hAC_zero : ∀ a h, h uv.2 ≠ a → Aop uv a * Cop uv a h = 0 := by
      intro a h ha
      simp [Cop, ha]
    have hBC_zero : ∀ a h, h uv.2 ≠ a → Bop uv a * Cop uv a h = 0 := by
      intro a h ha
      simp [Cop, ha]
    rw [hAvg (fun a h => Aop uv a * Cop uv a h) hAC_zero,
        hAvg (fun a h => Bop uv a * Cop uv a h) hBC_zero]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro h _
    have hCop_at : Cop uv (h uv.2) h =
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2)) := by
      simp [Cop]
    have hAop_at :
        Aop uv (h uv.2) = leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    have hBop_at :
        Bop uv (h uv.2) = rightTensor (ι₁ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    rw [hCop_at, hAop_at, hBop_at]
    rw [← ev_sub]
    congr 1
    noncomm_ring
  -- Average the pointwise identity, then conclude
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a h)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a h)) =
      addInUCSChainQ1 params strategy T - addInUCSChainQ0 params strategy T := by
    rw [addInU_cs_chain_step1_diff_eq params strategy T]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  -- Wrap up: use abs_sub_comm to reverse the subtraction order
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs

/-- Cauchy--Schwarz contraction side condition for Step 2.

For a fixed `(u, v)`, the left-tensor-sandwiched sum
`Σ_a (leftTensor A^v_a · K_{u,v,a}) · (leftTensor A^v_a · K_{u,v,a})ᴴ ≤ 1`
where `K_{u,v,a} = Σ_{h: h(v)=a} (M^u_h ⊗ T_h)`.  This is the C side condition
fed to `closenessOfInnerProduct_left` in the Step 2 raw bound proof. -/
private lemma addInU_step2_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0)) *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  set K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
      opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
        (T.outcome h)
  set Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    leftTensor (ι₂ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ h : Polynomial params,
          (if h uv.2 = a then
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h)
          else 0)) = Pa a * K a := by
    intro a
    have hfilter :
        (∑ h : Polynomial params,
          (if h uv.2 = a then
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                (T.outcome h)
          else 0)) =
            ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h uv.2 = a),
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h) := by
      rw [Finset.sum_filter]
    rw [hfilter, ← Finset.mul_sum]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hMh_herm : ∀ h : Polynomial params,
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)ᴴ =
          (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)).isHermitian.eq
    have hTh_herm : ∀ h : Polynomial params,
        (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hMh_herm, hTh_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, leftTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_mul_leftTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro h _
    exact opTensor_nonneg
      ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h)
      (T.outcome_pos h)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_filtered_sandwiched_tensor_sum_le_one params strategy T uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params,
      (Pa a * K a) * (Pa a * K a)ᴴ ≤ Pa a := by
    intro a
    have hexpand : (Pa a * K a) * (Pa a * K a)ᴴ = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := IsSelfAdjoint.conjugate_le_conjugate (hK_sq_le_one a) (hPa_herm a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [leftTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, leftTensor_one]
  calc
    ∑ a : Fq params,
        (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0)) *
          (∑ h : Polynomial params,
            (if h uv.2 = a then
              leftTensor (ι₂ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
                opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
                  (T.outcome h)
            else 0))ᴴ
        = ∑ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Raw `|Q₁ - Q₂| ≤ √(2δ)` bound for the add-in-u Step 2 Cauchy--Schwarz move.

Proves the paper's `eq:move-another` bound from
`references/ldt-paper/self_improvement.tex`, lines 279--297, as a completed
construction.  The proof combines the algebraic alignment
`addInU_cs_chain_step2_diff_eq` with the weighted Cauchy--Schwarz inner-product
bound `Preliminaries.closenessOfInnerProduct_left`, the `A^v` self-consistency
input via `addInU_pointMeasurement_snd_selfConsistency`, and the
filtered-tensor contraction `addInU_filtered_sandwiched_tensor_sum_le_one`. -/
lemma addInU_cs_chain_step2_abs_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
      Real.sqrt (2 * delta) := by
  classical
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a h =>
      if h uv.2 = a then
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h)
      else 0
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state (Aop uv) (Bop uv)) ≤ 2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rfl
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ h : Polynomial params, Cop uv a h) *
            (∑ h : Polynomial params, Cop uv a h)ᴴ) ≤ 1 :=
    fun uv => addInU_step2_C_contraction params strategy T uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_left
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Aop uv a)) -
        (∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Bop uv a)) =
      ∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (leftTensor (ι₂ := ι) Av *
            (opTensor Mh (T.outcome h) *
              (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av))) := by
    intro uv
    have hAvg : ∀ (X : Fq params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι)),
        (∀ a h, h uv.2 ≠ a → X a h = 0) →
        ∑ a : Fq params, ∑ h : Polynomial params, ev strategy.state (X a h) =
          ∑ h : Polynomial params, ev strategy.state (X (h uv.2) h) := by
      intro X hX
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro h _
      have hsingle : ∑ a : Fq params, ev strategy.state (X a h) =
          ev strategy.state (X (h uv.2) h) := by
        rw [Finset.sum_eq_single (h uv.2)]
        · intro a _ ha
          rw [hX a h (Ne.symm ha)]
          exact ev_zero strategy.state
        · intro hmem
          exact (hmem (Finset.mem_univ _)).elim
      exact hsingle
    have hCA_zero : ∀ a h, h uv.2 ≠ a → Cop uv a h * Aop uv a = 0 := by
      intro a h ha
      simp [Cop, ha]
    have hCB_zero : ∀ a h, h uv.2 ≠ a → Cop uv a h * Bop uv a = 0 := by
      intro a h ha
      simp [Cop, ha]
    rw [hAvg (fun a h => Cop uv a h * Aop uv a) hCA_zero,
        hAvg (fun a h => Cop uv a h * Bop uv a) hCB_zero]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro h _
    have hCop_at : Cop uv (h uv.2) h =
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2)) *
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
            (T.outcome h) := by
      simp [Cop]
    have hAop_at :
        Aop uv (h uv.2) = leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    have hBop_at :
        Bop uv (h uv.2) = rightTensor (ι₁ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2) := rfl
    rw [hCop_at, hAop_at, hBop_at]
    rw [← ev_sub]
    congr 1
    noncomm_ring
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Aop uv a)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (Cop uv a h * Bop uv a)) =
      addInUCSChainQ2 params strategy T - addInUCSChainQ1 params strategy T := by
    rw [addInU_cs_chain_step2_diff_eq params strategy T]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  -- Wrap up: use abs_sub_comm to reverse the subtraction order
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


