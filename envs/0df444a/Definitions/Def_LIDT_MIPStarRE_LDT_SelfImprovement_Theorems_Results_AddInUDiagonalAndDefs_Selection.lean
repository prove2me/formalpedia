-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:10:12.252489+00:00
-- url     : https://prove2.me/theorems/76bec9e6-52f4-4665-b279-f2722a693dbb
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUDiagonalAndDefs / Selection
-- statement:
--   This bundle supplies the diagonal selection and projector identities for the add-in-u self-consistency application. It identifies the release expression, inserts point projectors around helper outcomes, and records the averaged and one-sided forms used in the residual chain.
--
--   Principal definitions:
--   - `selfConsistencyAddInUSelection`: the diagonal selection used to apply the add-in-u strong self-consistency estimate.
--   - `addInURightQuantity_selfConsistencySelection_eq_release`: identification of the selected right quantity with the release expression.
--   - `proj_outer_sandwich_eq`: the projector identity `A (A X A) A = A X A`.
--   - `pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite`: insertion of a point projector around a sandwiched helper outcome as an indicator case split.
--   - `ev_opTensor_pointConditioned_sandwichedPolynomialOutcome_outer_eq_indicator`: the corresponding expectation identity.
--   - `polynomial_off_diagonal_outer_sandwich_eq_indicator_avg`: the averaged off-diagonal projector identity.
--   - `sandwichedPolynomialOutcome_mul_pointConditioned_eq_ite`: the right-multiplication form of the point-projector identity.
--   - `pointConditioned_sandwichedPolynomialOutcome_outer_eq_right`: the full outer point sandwich reduced to the one-sided delete-an-A form.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Selection.lean#L36-L715

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Selection.lean by skeleton subtraction.
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

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Diagonal add-in-u selection and point-sandwich endpoints

This module contains the diagonal selection used in the strong-self-consistency
application of the add-in-`u` lemma, the endpoint identities for its left and
right sides, the point-projector insertion identities, and the Schwartz--Zippel
collision endpoints used by the helper strong-self-consistency argument.

## References

- `references/ldt-paper/self_improvement.tex` lines 247--252, 455--468
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
/-- The diagonal selection used in the strong-self-consistency application of
`lem:add-in-u` in the proof of `lem:self-improvement-helper`.

At every point `u`, this selects exactly the pairs `(h, h)` of polynomial
outcomes, matching `self_improvement.tex`, lines 459--468. -/
noncomputable def selfConsistencyAddInUSelection (params : Parameters)
    [FieldModel params.q] : AddInUSelection params (Polynomial params) :=
  fun _ => {hh | hh.1 = hh.2}



private lemma addInURightOperatorAtPoint_selfConsistencySelection
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) (Polynomial params) ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    addInURightOperatorAtPoint params strategy M T (selfConsistencyAddInUSelection params) u =
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        opTensor (Au * (M u).outcome h * Au) (T.outcome h) := by
  classical
  unfold addInURightOperatorAtPoint selfConsistencyAddInUSelection addInUSelectionPairs
  symm
  refine Finset.sum_bij (fun h _ => (h, h)) ?_ ?_ ?_ ?_
  · intro h _
    simp
  · intro a _ _ _ hab
    exact congrArg Prod.fst hab
  · intro ah hah
    refine ⟨ah.1, Finset.mem_univ _, ?_⟩
    simp at hah
    ext <;> simp [hah]
  · intro h _
    simp



/-- The right side of the diagonal `add-in-u` application is the paper's
"release-the-kraken" expression, with the two copies of
`A^u_{h(u)}` placed around the pointwise helper submeasurement `H^u_h`. -/
lemma addInURightQuantity_selfConsistencySelection_eq_release
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h))) := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state (addInURightOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) u)) = _
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [addInURightOperatorAtPoint_selfConsistencySelection]
  exact ev_sum strategy.state _



/-- Projective sandwich collapse: if `A * A = A`, then `A * (A * X * A) * A = A * X * A`.

This is the operator-algebra fact used to simplify the diagonal `add-in-u`
right-hand side: the outer `A^u_{h(u)}` factors collapse into the inner
sandwich `A^u_{h(u)} T_h A^u_{h(u)}` because
`(strategy.pointMeasurement u).proj` makes every point-measurement outcome a
projection. -/
lemma proj_outer_sandwich_eq {ι : Type*} [Fintype ι]
    (A X : MIPStarRE.Quantum.Op ι) (hA : A * A = A) :
    A * (A * X * A) * A = A * X * A := by
  have h1 : A * (A * X * A) * A = (A * A) * X * (A * A) := by noncomm_ring
  rw [h1, hA]

/-- Insert the point projector around a sandwiched helper outcome.

For fixed `u`, the operator
`H^u_{h'} = A^u_{h'(u)} T_{h'} A^u_{h'(u)}` survives the outer sandwich by
`A^u_{h(u)}` precisely when the two polynomials agree at `u`.  This is the
operator form of the paper identity labelled `eq:h-blt`. -/
lemma pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (h h' : Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah =
      if h u = h' u then
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h'
      else
        0 := by
  classical
  by_cases heval : h u = h' u
  · rw [if_pos heval]
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    have hproj : Ah * Ah = Ah := by
      simpa [Ah, pointConditionedOutcomeOperatorAtPolynomial] using
        (strategy.pointMeasurement u).proj (h u)
    have houtcome :
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h' =
          Ah * T.outcome h' * Ah := by
      simp [sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt,
        pointConditionedOutcomeOperatorAtPolynomial, Ah, heval]
    rw [houtcome]
    exact proj_outer_sandwich_eq Ah (T.outcome h') hproj
  · rw [if_neg heval]
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    let Ah' := pointConditionedOutcomeOperatorAtPolynomial params strategy h' u
    have horth : Ah * Ah' = 0 := by
      simpa [Ah, Ah', pointConditionedOutcomeOperatorAtPolynomial] using
        ProjMeas.outcome_orthogonal (strategy.pointMeasurement u) (h u) (h' u) heval
    have houtcome :
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h' =
          Ah' * T.outcome h' * Ah' := by
      simp [sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt,
        pointConditionedOutcomeOperatorAtPolynomial, Ah']
    rw [houtcome]
    calc
      Ah * (Ah' * T.outcome h' * Ah') * Ah =
          (Ah * Ah') * T.outcome h' * Ah' * Ah := by noncomm_ring
      _ = 0 := by rw [horth]; simp

/-- Expectation form of the point-projector insertion identity.

This is the scalar version of
`pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite`, with the agreement
condition written as the real-valued indicator that appears in the paper's
off-diagonal residual estimate. -/
lemma ev_opTensor_pointConditioned_sandwichedPolynomialOutcome_outer_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (h h' : Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    ev strategy.state
        (opTensor
          (Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
          (T.outcome h)) =
      (if h u = h' u then (1 : Error) else 0) *
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
            (T.outcome h)) := by
  classical
  by_cases heval : h u = h' u
  · rw [if_pos heval]
    change ev strategy.state
        (opTensor
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
          (T.outcome h)) =
        1 * ev strategy.state
          (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
            (T.outcome h))
    rw [pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite]
    rw [if_pos heval, one_mul]
  · rw [if_neg heval]
    change ev strategy.state
        (opTensor
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
          (T.outcome h)) =
        0 * ev strategy.state
          (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
            (T.outcome h))
    rw [pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite]
    rw [if_neg heval, zero_mul]
    have hzeroTensor :
        opTensor (0 : MIPStarRE.Quantum.Op ι) (T.outcome h) = 0 := by
      ext i j
      simp [opTensor]
    rw [hzeroTensor, ev_zero]

/-- Averaged off-diagonal form of the paper identity `eq:h-blt`.

The left-hand side is the off-diagonal contribution after inserting the outer
point projector `A^u_{h(u)}`.  The right-hand side removes that outer sandwich
and records the surviving summands by the agreement indicator
`1_{h(u)=h'(u)}`. -/
theorem polynomial_off_diagonal_outer_sandwich_eq_indicator_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
            ev strategy.state
              (opTensor
                (Ah *
                  ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
                  Ah)
                (T.outcome h))) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            (if h u = h' u then (1 : Error) else 0) *
              ev strategy.state
                (opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
                  (T.outcome h))) := by
  classical
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  refine Finset.sum_congr rfl ?_
  intro h _
  refine Finset.sum_congr rfl ?_
  intro h' _
  exact
    ev_opTensor_pointConditioned_sandwichedPolynomialOutcome_outer_eq_indicator
      params strategy T u h h'

/-- Right multiplication form of the point-projector identity.

For a point `u`, multiplying the pointwise helper outcome `H^u_{h'}` on the
right by `A^u_{h(u)}` retains exactly the summands with `h(u)=h'(u)`.  Together
with `pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite`, this is the
operator identity used to pass from the enlarged outer-sandwich expression to
the paper's `eq:delete-an-A` form. -/
lemma sandwichedPolynomialOutcome_mul_pointConditioned_eq_ite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (h h' : Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah =
      if h u = h' u then
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h'
      else
        0 := by
  classical
  by_cases heval : h u = h' u
  · rw [if_pos heval]
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    have hproj : Ah * Ah = Ah := by
      simpa [Ah, pointConditionedOutcomeOperatorAtPolynomial] using
        (strategy.pointMeasurement u).proj (h u)
    have houtcome :
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h' =
          Ah * T.outcome h' * Ah := by
      simp [sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt,
        pointConditionedOutcomeOperatorAtPolynomial, Ah, heval]
    rw [houtcome]
    calc
      (Ah * T.outcome h' * Ah) * Ah =
          Ah * T.outcome h' * (Ah * Ah) := by noncomm_ring
      _ = Ah * T.outcome h' * Ah := by rw [hproj]
  · rw [if_neg heval]
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    let Ah' := pointConditionedOutcomeOperatorAtPolynomial params strategy h' u
    have hrev : ¬ h' u = h u := fun hv => heval hv.symm
    have horth : Ah' * Ah = 0 := by
      simpa [Ah, Ah', pointConditionedOutcomeOperatorAtPolynomial] using
        ProjMeas.outcome_orthogonal (strategy.pointMeasurement u) (h' u) (h u) hrev
    have houtcome :
        (sandwichedPolynomialSubMeasAt params strategy T u).outcome h' =
          Ah' * T.outcome h' * Ah' := by
      simp [sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt,
        pointConditionedOutcomeOperatorAtPolynomial, Ah']
    rw [houtcome]
    calc
      (Ah' * T.outcome h' * Ah') * Ah =
          Ah' * T.outcome h' * (Ah' * Ah) := by noncomm_ring
      _ = 0 := by rw [horth]; simp

/-- The full outer point-sandwich equals the one-sided `delete-an-A` form.

This is the operator identity underlying the paper's passage from the enlarged
sum in `eq:threw-in-h-prime` to `eq:delete-an-A`. -/
lemma pointConditioned_sandwichedPolynomialOutcome_outer_eq_right
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (h h' : Polynomial params) :
    let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
    Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah =
      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah := by
  classical
  change pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
      pointConditionedOutcomeOperatorAtPolynomial params strategy h u =
    ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
      pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  rw [pointConditioned_sandwichedPolynomialOutcome_outer_eq_ite]
  rw [sandwichedPolynomialOutcome_mul_pointConditioned_eq_ite]

/-- Schwartz--Zippel bound for the point-measurement sandwich collision term.

After the two variance swaps in the helper strong self-consistency proof, the
polynomial-agreement indicator is independent of the point `v` at which the
outer point measurement is evaluated.  Averaging over `v`, the tensor-form
Schwartz--Zippel estimate from the preliminaries bounds the whole collision
term by `m d / q`. -/
theorem polynomial_collision_pointMeasurement_sandwichTensor_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun v =>
        ∑ gg : Polynomial params × Polynomial params,
          ∑ a : Fq params,
            (if gg.1 = gg.2 then 0 else
              avgOver (uniformDistribution (Point params))
                (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
              ev strategy.state
                (opTensor
                  ((strategy.pointMeasurement v).outcome a *
                    T.outcome gg.1 *
                    (strategy.pointMeasurement v).outcome a)
                  (T.outcome gg.2))) ≤
      (params.m * params.d : Error) / params.q := by
  classical
  let δ : Error := (params.m * params.d : Error) / params.q
  have hpointwise : ∀ v : Point params,
      (∑ gg : Polynomial params × Polynomial params,
          ∑ a : Fq params,
            (if gg.1 = gg.2 then 0 else
              avgOver (uniformDistribution (Point params))
                (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
              ev strategy.state
                (opTensor
                  ((strategy.pointMeasurement v).outcome a *
                    T.outcome gg.1 *
                    (strategy.pointMeasurement v).outcome a)
                  (T.outcome gg.2))) ≤ δ := by
    intro v
    let Outer : SubMeas (Fq params) ι :=
      (strategy.pointMeasurement v).toSubMeas
    have hcollision :=
      Preliminaries.polynomialCollision_sandwichTensor_le_mdq
        (params := params) (ψ := strategy.state) (hnorm := strategy.isNormalized)
        (Outer := Outer) (Inner := T) (Right := T)
    simpa [δ, Outer, pointConditionedOutcomeOperatorAtPolynomial,
      leftTensor_mul_rightTensor_eq_opTensor] using hcollision
  exact avgOver_uniform_le_const _ δ hpointwise

/-- Schwartz--Zippel bound for the selected off-diagonal residual endpoint.

This is the endpoint used after the variance swaps in the helper
strong-self-consistency residual estimate.  The selected outer point-measurement
outcome `A^v_{h(v)}` is bounded by the full sum over field outcomes in
`polynomial_collision_pointMeasurement_sandwichTensor_avg_le_mdq`. -/
theorem polynomial_off_diagonal_swapped_indicator_sandwich_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun v =>
        ∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            avgOver (uniformDistribution (Point params))
                (fun u => if h u = h' u then (1 : Error) else 0) *
              ev strategy.state
                (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                    T.outcome h' *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (T.outcome h))) ≤
      (params.m * params.d : Error) / params.q := by
  classical
  let fullCollision : Point params → Error := fun v =>
    ∑ gg : Polynomial params × Polynomial params,
      ∑ a : Fq params,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev strategy.state
            (opTensor
              ((strategy.pointMeasurement v).outcome a *
                T.outcome gg.1 *
                (strategy.pointMeasurement v).outcome a)
              (T.outcome gg.2))
  have hselected_le_full : ∀ v : Point params,
      (∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            avgOver (uniformDistribution (Point params))
                (fun u => if h u = h' u then (1 : Error) else 0) *
              ev strategy.state
                (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                    T.outcome h' *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (T.outcome h))) ≤ fullCollision v := by
    intro v
    let Outer : SubMeas (Fq params) ι :=
      (strategy.pointMeasurement v).toSubMeas
    let F : Fq params → Polynomial params → Polynomial params → Error :=
      fun a i r =>
        (if i = r then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if i u = r u then (1 : Error) else 0)) *
          ev strategy.state
            (opTensor
              (Outer.outcome a * T.outcome i * Outer.outcome a)
              (T.outcome r))
    have hF_nonneg : ∀ a i r, 0 ≤ F a i r := by
      intro a i r
      have hcoef_nonneg :
          0 ≤
            (if i = r then 0 else
              avgOver (uniformDistribution (Point params))
                (fun u => if i u = r u then (1 : Error) else 0)) := by
        by_cases hir : i = r
        · rw [if_pos hir]
        · rw [if_neg hir]
          exact avgOver_nonneg _ _ fun u => by
            by_cases hu : i u = r u
            · rw [if_pos hu]
              norm_num
            · rw [if_neg hu]
      have hsummand_nonneg :
          0 ≤ ev strategy.state
            (opTensor (Outer.outcome a * T.outcome i * Outer.outcome a)
              (T.outcome r)) := by
        simpa [F, Outer, leftTensor_mul_rightTensor_eq_opTensor] using
          sandwichTensorSummand_nonneg strategy.state Outer T T a i r
      exact mul_nonneg hcoef_nonneg hsummand_nonneg
    have hselected_eq :
        (∑ h : Polynomial params,
            ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
              avgOver (uniformDistribution (Point params))
                  (fun u => if h u = h' u then (1 : Error) else 0) *
                ev strategy.state
                  (opTensor
                    (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                      T.outcome h' *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                    (T.outcome h))) =
          ∑ h : Polynomial params,
            ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
              F (h v) h' h := by
      refine Finset.sum_congr rfl ?_
      intro h _
      refine Finset.sum_congr rfl ?_
      intro h' hh'
      have hne : h' ≠ h := by
        exact (Finset.mem_erase.mp hh').1
      have hcoef :
          avgOver (uniformDistribution (Point params))
              (fun u => if h u = h' u then (1 : Error) else 0) =
            avgOver (uniformDistribution (Point params))
              (fun u => if h' u = h u then (1 : Error) else 0) := by
        refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
        intro u
        by_cases hu : h u = h' u
        · rw [if_pos hu, if_pos hu.symm]
        · have hrev : ¬ h' u = h u := fun hv => hu hv.symm
          rw [if_neg hu, if_neg hrev]
      rw [hcoef]
      simp [F, Outer, pointConditionedOutcomeOperatorAtPolynomial, hne]
    calc
      (∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            avgOver (uniformDistribution (Point params))
                (fun u => if h u = h' u then (1 : Error) else 0) *
              ev strategy.state
                (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                    T.outcome h' *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (T.outcome h)))
        = ∑ h : Polynomial params,
            ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
              F (h v) h' h := hselected_eq
      _ ≤ ∑ h : Polynomial params,
            ∑ h' : Polynomial params, F (h v) h' h := by
          refine Finset.sum_le_sum ?_
          intro h _
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset h Finset.univ)
            (fun h' _ _ => hF_nonneg (h v) h' h)
      _ ≤ ∑ h : Polynomial params,
            ∑ h' : Polynomial params, ∑ a : Fq params, F a h' h := by
          refine Finset.sum_le_sum ?_
          intro h _
          refine Finset.sum_le_sum ?_
          intro h' _
          exact Finset.single_le_sum
            (fun a _ => hF_nonneg a h' h) (Finset.mem_univ (h v))
      _ = fullCollision v := by
          simp only [fullCollision, F, Outer]
          rw [Finset.sum_comm]
          rw [Fintype.sum_prod_type]
  have havg_le_full :
      avgOver (uniformDistribution (Point params)) (fun v =>
          ∑ h : Polynomial params,
            ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
              avgOver (uniformDistribution (Point params))
                  (fun u => if h u = h' u then (1 : Error) else 0) *
                ev strategy.state
                  (opTensor
                    (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                      T.outcome h' *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                    (T.outcome h))) ≤
        avgOver (uniformDistribution (Point params)) fullCollision := by
    exact avgOver_mono _ _ _ hselected_le_full
  have hfull :
      avgOver (uniformDistribution (Point params)) fullCollision ≤
        (params.m * params.d : Error) / params.q := by
    simpa [fullCollision] using
      polynomial_collision_pointMeasurement_sandwichTensor_avg_le_mdq params strategy T
  exact havg_le_full.trans hfull


/-- Projective simplification of the diagonal `add-in-u` right operator at a point.

Combining `addInURightOperatorAtPoint_selfConsistencySelection` with the
projectivity of `strategy.pointMeasurement` (each `A^u_a * A^u_a = A^u_a`),
the at-point operator collapses to the simpler tensor sum
`Σ_h H^u_h ⊗ T_h` where `H^u_h = sandwichedPolynomialSubMeasAt T u h`. -/
private lemma addInURightOperatorAtPoint_selfConsistencySelection_proj_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    addInURightOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) u =
      ∑ h : Polynomial params,
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
          (T.outcome h) := by
  classical
  rw [addInURightOperatorAtPoint_selfConsistencySelection]
  refine Finset.sum_congr rfl ?_
  intro h _
  -- Unfold the `let Au := ...` binder produced by
  -- `addInURightOperatorAtPoint_selfConsistencySelection` so that we can
  -- expand the inner sandwich `(M u).outcome h = Au * T_h * Au`.
  change opTensor
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
        ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h) *
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
      (T.outcome h) =
    opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
      (T.outcome h)
  have hproj :
      pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u =
      pointConditionedOutcomeOperatorAtPolynomial params strategy h u := by
    simpa [pointConditionedOutcomeOperatorAtPolynomial] using
      (strategy.pointMeasurement u).proj (h u)
  have hsandwich :
      (sandwichedPolynomialSubMeasAt params strategy T u).outcome h =
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
          T.outcome h *
          pointConditionedOutcomeOperatorAtPolynomial params strategy h u := by
    rfl
  rw [hsandwich]
  congr 1
  exact proj_outer_sandwich_eq _ _ hproj

/-- Projective simplification of the diagonal `add-in-u` right quantity.

This is the projection-collapsed paper expression: the two outer
`A^u_{h(u)}` factors absorb into the inner sandwich `H^u_h = A^u_{h(u)}
T_h A^u_{h(u)}`, leaving the cleaner form
`E_u Σ_h ⟨ψ, H^u_h ⊗ T_h ψ⟩` used in the simplified scalar transfer. -/
lemma addInURightQuantity_selfConsistencySelection_eq_simplified
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state (addInURightOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) u)) = _
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [addInURightOperatorAtPoint_selfConsistencySelection_proj_eq]
  exact ev_sum strategy.state _


end MIPStarRE.LDT.SelfImprovement

end

end LIDT


