-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:13:18.472965+00:00
-- url     : https://prove2.me/theorems/fad38a98-9e9b-4449-8660-0b1b6f9c65a2
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / AddInUDiagonalAndDefs / Residual
-- statement:
--   This bundle defines the scalar and operator quantities in the diagonal add-in-u residual argument. The definitions track insertion of the outer point projector, indicator replacement, variance swaps, deletion and cloning of that projector, and movement to the opposite tensor register.
--
--   Principal definitions:
--   - `helperOffDiagonalOuterSandwichQuantity`: the off-diagonal helper contribution with the outer point projector inserted.
--   - `helperOffDiagonalIndicatorQuantity`: the same contribution after replacing the outer projector by the polynomial-agreement indicator.
--   - `helperOffDiagonalOneSidedSwappedIndicatorQuantity`: the intermediate expression after the first variance swap.
--   - `helperOffDiagonalSwappedIndicatorQuantity`: the endpoint after the variance swaps.
--   - `helperFullOuterSandwichQuantity`: the enlarged full expression with the outer point projector inserted.
--   - `helperDeleteAQuantity`: the full expression after deleting the left point projector.
--   - `helperDeleteAClonedQuantity`: the deleted-projector expression after replacing the remaining point by an independent point.
--   - `helperMoveOverVQuantity`: the expression after moving the remaining point projector to the right tensor factor.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Residual.lean#L32-L440

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUDiagonalAndDefs/Residual.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
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
# Off-diagonal residual estimates for the helper SSC argument

This module names the off-diagonal scalar quantities appearing after the
projector insertion in the helper strong-self-consistency proof, records their
exact decompositions, and assembles the two variance-transport comparisons with
the Schwartz--Zippel endpoint.

## References

- `references/ldt-paper/self_improvement.tex` lines 455--468
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
/-! ### Off-diagonal residual quantities for the helper SSC estimate -/

/-- The off-diagonal contribution after inserting the outer point projector
`A^u_{h(u)}` around the pointwise helper outcome `H^u_{h'}`.

This is the non-diagonal term added when the diagonal released expression is
enlarged to the full `(h,h')` sum in the proof of helper strong
self-consistency. -/
noncomputable def helperOffDiagonalOuterSandwichQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
        let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        ev strategy.state
          (opTensor
            (Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
            (T.outcome h)))

/-- The same off-diagonal contribution after using `eq:h-blt`: the outer
projector has been removed from the operator and replaced by the polynomial
agreement indicator `1_{h(u)=h'(u)}`. -/
noncomputable def helperOffDiagonalIndicatorQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
        (if h u = h' u then (1 : Error) else 0) *
          ev strategy.state
            (opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
              (T.outcome h)))

/-- The intermediate off-diagonal expression after the first variance swap.

The left copy of the point projector has been evaluated at an independent point
`v`, while the right copy is still evaluated at the original point `u`.  This is
the Lean scalar form of the expression in the paper immediately after
`eq:swapped-u-for-v`. -/
noncomputable def helperOffDiagonalOneSidedSwappedIndicatorQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
        (if h uv.1 = h' uv.1 then (1 : Error) else 0) *
          ev strategy.state
            (opTensor
              (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 *
                T.outcome h' *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)
              (T.outcome h)))

/-- The post-variance-swap endpoint for the off-diagonal contribution.

Here both copies of the point projector have been evaluated at an independent
point `v`, while the agreement indicator has already been averaged over the
original point `u`.  This is the scalar expression to which the
Schwartz--Zippel estimate is applied. -/
noncomputable def helperOffDiagonalSwappedIndicatorQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
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
              (T.outcome h)))

/-- The full enlarged expression after inserting the outer point projector.

This includes both the diagonal and off-diagonal pairs `(h,h')`, and is the
right-hand side of `eq:threw-in-h-prime` before applying `eq:h-blt`. -/
noncomputable def helperFullOuterSandwichQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ∑ h' : Polynomial params,
        let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        ev strategy.state
          (opTensor
            (Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
            (T.outcome h)))

/-- The full inserted expression splits into its released diagonal part and its
off-diagonal remainder.

This is the finite-sum identity underlying the passage from
`eq:release-the-kraken` to `eq:threw-in-h-prime`: for each fixed polynomial
`h`, the sum over all `h'` is the diagonal term `h' = h` plus the sum over
`h' ≠ h`. -/
theorem helperFullOuterSandwichQuantity_eq_release_add_offDiagonalOuterSandwichQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperFullOuterSandwichQuantity params strategy T =
      addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) +
      helperOffDiagonalOuterSandwichQuantity params strategy T := by
  classical
  rw [addInURightQuantity_selfConsistencySelection_eq_release,
    helperFullOuterSandwichQuantity, helperOffDiagonalOuterSandwichQuantity]
  rw [← avgOver_add]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Polynomial params))
    (fun h' =>
      let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
      ev strategy.state
        (opTensor
          (Ah * ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
          (T.outcome h)))
    (Finset.mem_univ h)]
  ring

/-- The full enlarged expression after deleting the left copy of the point
projector.

This is the paper's `eq:delete-an-A` scalar quantity. -/
noncomputable def helperDeleteAQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ∑ h' : Polynomial params,
        let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        ev strategy.state
          (opTensor
            (((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
            (T.outcome h)))

/-- Formal version of the paper's `eq:delete-an-A` identity. -/
theorem helperFullOuterSandwichQuantity_eq_deleteAQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperFullOuterSandwichQuantity params strategy T =
      helperDeleteAQuantity params strategy T := by
  classical
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  refine Finset.sum_congr rfl ?_
  intro h _
  refine Finset.sum_congr rfl ?_
  intro h' _
  change ev strategy.state
      (opTensor
        (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
          ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
          pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
        (T.outcome h)) =
    ev strategy.state
      (opTensor
        (((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') *
          pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
        (T.outcome h))
  rw [pointConditioned_sandwichedPolynomialOutcome_outer_eq_right]

/-- The `delete-an-A` expression after replacing the remaining point projector
by an independent point.

This is the scalar quantity on the right-hand side of the paper's
`eq:swap-u-for-v-attack-of-the-clones`. -/
noncomputable def helperDeleteAClonedQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      ∑ h' : Polynomial params,
        ev strategy.state
          (opTensor
            (((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h') *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
            (T.outcome h)))

/-- The expression obtained after moving the remaining point projector to the
right tensor factor.

This is the scalar quantity on the right-hand side of the paper's
`eq:move-over-v`. -/
noncomputable def helperMoveOverVQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      ∑ h' : Polynomial params,
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h')
            (T.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)))



/-- The reverse scalar direction of the post-`delete-an-A` transport estimates.

This is the direction used when the final `move-over-v` expression is known to
be large and one transfers that lower bound back to the `delete-an-A` expression.
It is again only the triangle-inequality assembly of the two analytic transport
estimates. -/
theorem helperMoveOverVQuantity_le_deleteA_of_abs_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hclone :
      |helperDeleteAQuantity params strategy T -
        helperDeleteAClonedQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T -
        helperMoveOverVQuantity params strategy T| ≤
          Real.sqrt (2 * delta)) :
    helperMoveOverVQuantity params strategy T ≤
      helperDeleteAQuantity params strategy T +
        Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) := by
  have hclone_ge :
      -Real.sqrt (selfImprovementVarianceError params eps delta) ≤
          helperDeleteAQuantity params strategy T -
            helperDeleteAClonedQuantity params strategy T :=
    (abs_le.mp hclone).1
  have hmove_ge :
      -Real.sqrt (2 * delta) ≤
          helperDeleteAClonedQuantity params strategy T -
            helperMoveOverVQuantity params strategy T :=
    (abs_le.mp hmove).1
  linarith

/-- Named form of the identity `eq:h-blt` for the off-diagonal helper SSC
quantity. -/
theorem helperOffDiagonalOuterSandwichQuantity_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperOffDiagonalOuterSandwichQuantity params strategy T =
      helperOffDiagonalIndicatorQuantity params strategy T := by
  simpa [helperOffDiagonalOuterSandwichQuantity, helperOffDiagonalIndicatorQuantity]
    using polynomial_off_diagonal_outer_sandwich_eq_indicator_avg params strategy T

/-- Named Schwartz--Zippel endpoint for the helper SSC off-diagonal term. -/
theorem helperOffDiagonalSwappedIndicatorQuantity_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperOffDiagonalSwappedIndicatorQuantity params strategy T ≤
      (params.m * params.d : Error) / params.q := by
  simpa [helperOffDiagonalSwappedIndicatorQuantity] using
    polynomial_off_diagonal_swapped_indicator_sandwich_avg_le_mdq params strategy T

/-- Assemble the two one-projector variance transports for the off-diagonal
helper residual.

The first hypothesis is the estimate for replacing the left copy of
`A^u_{h(u)}` by `A^v_{h(v)}`.  The second hypothesis is the estimate for
replacing the remaining right copy by the same independent point `v`.  Together
they give the transport inequality used before the Schwartz--Zippel endpoint in
the proof of helper strong self-consistency. -/
theorem helperOffDiagonalIndicatorQuantity_le_swapped_of_abs_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalIndicatorQuantity params strategy T ≤
      helperOffDiagonalSwappedIndicatorQuantity params strategy T +
        2 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hleft_le :
      helperOffDiagonalIndicatorQuantity params strategy T -
          helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) :=
    (abs_le.mp hleft).2
  have hright_le :
      helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
          helperOffDiagonalSwappedIndicatorQuantity params strategy T ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) :=
    (abs_le.mp hright).2
  linarith

/-- Assemble the off-diagonal projector-insertion bound from the two variance
swaps and the Schwartz--Zippel endpoint.

The hypothesis `htransport` is precisely the analytic content of the two
Cauchy--Schwarz variance moves in the proof of
`item:self-improvement-self`: it transports the indicator form of the
off-diagonal term to the endpoint with both point projectors evaluated at the
independent point `v`.  The conclusion is the corresponding paper estimate
before substituting the concrete value of the transport error. -/
theorem helperOffDiagonalOuterSandwichQuantity_le_of_swapped_transport
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (η : Error)
    (htransport :
      helperOffDiagonalIndicatorQuantity params strategy T ≤
        helperOffDiagonalSwappedIndicatorQuantity params strategy T + η) :
    helperOffDiagonalOuterSandwichQuantity params strategy T ≤
      η + (params.m * params.d : Error) / params.q := by
  rw [helperOffDiagonalOuterSandwichQuantity_eq_indicator]
  have hsz := helperOffDiagonalSwappedIndicatorQuantity_le_mdq params strategy T
  linarith

/-- Paper-shaped form of the off-diagonal projector-insertion estimate.

Once the two variance swaps have supplied transport error
`2√ζ_variance`, the inserted off-diagonal contribution is bounded by
`2√ζ_variance + md/q`. -/
theorem helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (htransport :
      helperOffDiagonalIndicatorQuantity params strategy T ≤
        helperOffDiagonalSwappedIndicatorQuantity params strategy T +
          2 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalOuterSandwichQuantity params strategy T ≤
      2 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        (params.m * params.d : Error) / params.q :=
  helperOffDiagonalOuterSandwichQuantity_le_of_swapped_transport
    params strategy T (2 * Real.sqrt (selfImprovementVarianceError params eps delta))
    htransport

/-- Paper-shaped off-diagonal bound from the two explicit variance transports.

This version exposes the two Cauchy--Schwarz/global-variance moves separately:
first from the indicator form to the one-sided swapped expression, and then from
the one-sided swapped expression to the Schwartz--Zippel endpoint. -/
theorem helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq_of_abs_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalOuterSandwichQuantity params strategy T ≤
      2 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        (params.m * params.d : Error) / params.q :=
  helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq
    params strategy eps delta T
    (helperOffDiagonalIndicatorQuantity_le_swapped_of_abs_transports
      params strategy eps delta T hleft hright)


end MIPStarRE.LDT.SelfImprovement

end

end LIDT


