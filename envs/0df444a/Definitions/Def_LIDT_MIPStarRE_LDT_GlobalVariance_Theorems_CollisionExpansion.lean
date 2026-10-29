-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:59:11.889455+00:00
-- url     : https://prove2.me/theorems/8a6cedb7-8f18-425e-8c6f-e9a4f1292c8a
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / CollisionExpansion
-- statement:
--   This bundle develops the collision expansion for axis-parallel line questions. It reparametrizes incident line and point samples, marginalizes to the native base-point distribution, expands the postprocessed collision integrand, and establishes nonnegativity and total-mass bounds for the resulting tensor terms.
--
--   Principal definitions:
--   - `axisParallelLineQuestionParameterEquiv`: identifies an incident line question with a line and affine parameter.
--   - `avgOver_axisParallelLineQuestionDistribution`: rewrites the question distribution using line and parameter seeds.
--   - `axisParallelLinePointParamEquiv`: reindexes a line representative by its sampled point.
--   - `avgOver_axisParallelLinePointParam`: marginalizes to a point and direction presentation.
--   - `avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample`: identifies the native base-point test distribution.
--   - `generalizeBCollisionSeed_integrand`: expands the seeded postprocessed collision event.
--   - `generalizeBLineCollisionTensorMass_nonneg`: proves nonnegativity of the collision tensor mass.
--   - `generalizeBLineCollisionTensorMass_sum_le_one`: bounds its total mass by one.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean#L24-L549

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
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
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-! # Collision expansion and Schwartz-Zippel bounds

This module contains the `generalizeB` theorem wrappers, finite reparametrization
and distribution bookkeeping, and the Schwartz-Zippel collision expansion that
bounds the line-collision residual.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

private lemma generalizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy ψbi G := by
  refine
    { aggregateFamilyComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (axisParallelLineQuestionDistribution params)
          (generalizeBLeftFamily params strategy G)
          (generalizeBRightFamily params strategy G)
          (fun qu g =>
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
          (fun qu g =>
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
          (by
            intro qu
            simp [generalizeBLeftFamily])
          (by
            intro qu
            simp [generalizeBRightFamily])
          (generalizeBError params) (by
            intro g
            simpa [generalizeBDeviationAtPolynomial] using hpoint g)
      pointwiseNormBound := hpoint
      averagedNormBound :=
        avgOver_polynomialDistribution_le_of_pointwise params
          (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)
          (generalizeBError params) hpoint }



/-- The finite reparametrization of incident axis-parallel line questions by a
line `ℓ` and affine parameter `t`, sending `(ℓ,t)` to `(ℓ, ℓ(t))`. -/
private noncomputable def axisParallelLineQuestionParameterEquiv (params : Parameters)
    [FieldModel params.q] :
    AxisParallelLine params × Fq params ≃
      {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} where
  toFun := fun ℓt => ⟨(ℓt.1, ℓt.1.pointAt ℓt.2), ⟨ℓt.2, rfl⟩⟩
  invFun := fun qu => (qu.1.1, axisParallelLineQuestionParameter qu.1)
  left_inv := fun
    | ⟨ℓ, t⟩ => by
        simp [axisParallelLineQuestionParameter_pointAt]
  right_inv := fun
    | ⟨⟨ℓ, u⟩, ⟨t, ht⟩⟩ => by
        apply Subtype.ext
        dsimp only
        have hparam : axisParallelLineQuestionParameter (ℓ, u) = t := by
          calc
            axisParallelLineQuestionParameter (ℓ, u) =
                axisParallelLineQuestionParameter (ℓ, ℓ.pointAt t) := by rw [ht]
            _ = t := axisParallelLineQuestionParameter_pointAt ℓ t
        ext <;> simp [hparam, ht]

/-- Reindex the axis-parallel line-question distribution as a uniform average over
line/parameter seeds `(ℓ,t)` with sampled point `u = ℓ(t)`.

This is the distributional bookkeeping used in `expansion.tex`, lines 281--288. -/
lemma avgOver_axisParallelLineQuestionDistribution
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (axisParallelLineQuestionDistribution params) f =
      avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
  classical
  let e := axisParallelLineQuestionParameterEquiv params
  simpa [axisParallelLineQuestionDistribution, e, axisParallelLineQuestionParameterEquiv] using
    (avgOver_uniformOnFinset_filter_equiv
      (α := AxisParallelLineQuestion params)
      (β := AxisParallelLine params × Fq params)
      (p := pointOnLine (params := params))
      (e := e)
      (f := f))

/-- Reindex a line representative and affine parameter by the sampled point on
that line, keeping the direction and parameter as auxiliary data.

This is the finite bookkeeping behind `expansion.tex`, lines 300--302: averaging
over a line representative `ℓ` and a parameter `t` is the same as averaging over
the sampled base point `u = ℓ(t)`, the direction, and the forgotten parameter. -/
noncomputable def axisParallelLinePointParamEquiv (params : Parameters)
    [FieldModel params.q] :
    AxisParallelLine params × Fq params ≃ AxisParallelTestSample params × Fq params where
  toFun := fun ℓt => ((ℓt.1.pointAt ℓt.2, ℓt.1.direction), ℓt.2)
  invFun := fun st =>
    (({ base := fun j => if j = st.1.2 then subCoord (st.1.1 j) st.2 else st.1.1 j,
        direction := st.1.2 } : AxisParallelLine params), st.2)
  left_inv := fun
    | ⟨⟨base, direction⟩, t⟩ => by
      simp only [Prod.mk.injEq, AxisParallelLine.mk.injEq, and_true]
      funext j
      by_cases hj : j = direction <;>
        simp [AxisParallelLine.pointAt, hj, subCoord_addCoord_right]
  right_inv := fun
    | ⟨⟨u, direction⟩, t⟩ => by
      simp only [Prod.mk.injEq, and_true]
      ext j
      by_cases hj : j = direction <;>
        simp [AxisParallelLine.pointAt, hj]

/-- Marginalizing the uniform line/parameter presentation to the sampled point
and direction gives the native axis-parallel base-point test distribution. -/
private lemma avgOver_axisParallelLinePointParam
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelTestSample params → Error) :
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
      (fun ℓt => f (ℓt.1.pointAt ℓt.2, ℓt.1.direction)) =
    avgOver (uniformDistribution (AxisParallelTestSample params)) f := by
  let e := axisParallelLinePointParamEquiv params
  calc
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt => f (ℓt.1.pointAt ℓt.2, ℓt.1.direction))
      = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun st => f ((e.symm st).1.pointAt (e.symm st).2, (e.symm st).1.direction)) := by
          exact avgOver_uniform_equiv (e := e)
            (f := fun ℓt : AxisParallelLine params × Fq params =>
              f (ℓt.1.pointAt ℓt.2, ℓt.1.direction))
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun st => f st.1) := by
          apply avgOver_congr
          intro st
          have h := congrArg Prod.fst (e.right_inv st)
          exact congrArg f h
    _ = avgOver (uniformDistribution (AxisParallelTestSample params)) f :=
        avgOver_uniform_fst f

/-- Combining the incident-pair distribution with the sampled-point marginal gives
the native base-point test distribution. -/
lemma avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelTestSample params → Error) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu => f (qu.2, qu.1.direction)) =
    avgOver (uniformDistribution (AxisParallelTestSample params)) f := by
  rw [avgOver_axisParallelLineQuestionDistribution]
  exact avgOver_axisParallelLinePointParam params f

/-- Expanding the postprocessed collision event at the seeded question
`(ℓ, ℓ(t))` gives the line-answer sum from `expansion.tex`, lines 283--286. -/
private lemma generalizeBCollisionSeed_integrand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    ev ψbi (opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t))
        (G.outcome g)) =
      ∑ f : AxisLinePolynomial params,
        (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : Error)
        else 0) *
          ev ψbi (opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)) := by
  classical
  unfold generalizeBCollisionOperatorAtPolynomial generalizeBCollisionEventSubMeasAtPolynomial
    generalizeBCollisionEventProjMeasAtPolynomial
  simp only [ProjMeas.postprocess, postprocess, axisParallelLineQuestionParameter_pointAt,
    Polynomial.restrictToAxisParallelLine_apply]
  rw [opTensor_sum_left_finset]
  rw [ev_finset_sum]
  simp [Finset.sum_filter]

/-- Positivity of the tensor mass appearing in the line-collision expansion. -/
lemma generalizeBLineCollisionTensorMass_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    0 ≤ ev strategy.state (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
      (G.outcome g)) := by
  simpa [leftTensor_mul_rightTensor_eq_opTensor] using
    ev_leftTensor_mul_rightTensor_nonneg strategy.state
      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome_pos f)
      (G.outcome_pos g)

/-- The total tensor mass left after summing over line answers is at most one.

This is the normalization half of `expansion.tex`, lines 286--288: the
left-register line measurement sums to its total operator, the right-register
operator is the single submeasurement outcome `G_g ≤ 1`, and the strategy state
is normalized. -/
private lemma generalizeBLineCollisionTensorMass_sum_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (ℓ : AxisParallelLine params) :
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
        (G.outcome g))) ≤ 1 := by
  let B := (strategy.axisParallelMeasurement ℓ).toSubMeas
  calc
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor (B.outcome f) (G.outcome g)))
      = ev strategy.state (∑ f : AxisLinePolynomial params,
          opTensor (B.outcome f) (G.outcome g)) := by
          rw [ev_sum]
    _ = ev strategy.state (leftTensor (ι₂ := ι) B.total *
          rightTensor (ι₁ := ι) (G.outcome g)) := by
          congr 1
          calc
            (∑ f : AxisLinePolynomial params, opTensor (B.outcome f) (G.outcome g))
              = ∑ f : AxisLinePolynomial params,
                  leftTensor (ι₂ := ι) (B.outcome f) *
                    rightTensor (ι₁ := ι) (G.outcome g) := by
                    simp [leftTensor_mul_rightTensor_eq_opTensor]
            _ = (∑ f : AxisLinePolynomial params, leftTensor (ι₂ := ι) (B.outcome f)) *
                  rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [Finset.sum_mul]
            _ = leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ B.outcome]
                    rw [B.sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          apply ev_mono strategy.state _ _
          calc
            leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g)
              = opTensor B.total (G.outcome g) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ι) B.total :=
                  opTensor_le_leftTensor (SubMeas.total_nonneg B) (SubMeas.outcome_le_one G g)
            _ ≤ 1 := leftTensor_le_one (ι₂ := ι) B.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized

/-- Schwartz--Zippel coefficient bound for a fixed polynomial, line, and line answer. -/
lemma generalizeBLineCollisionCoefficient_le
    (params : Parameters)
    [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    avgOver (uniformDistribution (Fq params))
      (fun t =>
        if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : Error)
        else 0) ≤ generalizeBError params := by
  classical
  let h := Polynomial.restrictToAxisParallelLine params g ℓ
  let δ := generalizeBError params
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, generalizeBError]
    positivity
  by_cases hneq : f.poly ≠ h.poly
  · have hline := axisLinePolynomialAgreement_avg_le_mdq params f h hneq
    simpa [h, δ, generalizeBError, hneq] using hline
  · rw [show
        avgOver (uniformDistribution (Fq params))
          (fun t =>
            if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
              (1 : Error)
            else 0) = 0 by
          simpa [h, hneq] using (avgOver_zero (uniformDistribution (Fq params)))]
    exact hδ_nonneg

/-- Commuting the uniform parameter average past the finite sum over line answers.

This is the purely finite-sum bookkeeping between the paper's seed average over
`(ℓ,t)` and the coefficient-weighted display in `expansion.tex`, lines 286--288.
The remaining #753 residual is now only the incident-question/postprocess equality
between `generalizeBCollisionResidual` and `generalizeBSeedCollisionExpansion`. -/
lemma generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy ψbi G g =
      generalizeBLineCollisionExpansion params strategy ψbi G g := by
  classical
  unfold generalizeBSeedCollisionExpansion generalizeBLineCollisionExpansion
  calc
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt =>
          ∑ f : AxisLinePolynomial params,
            (if f ℓt.2 = (Polynomial.restrictToAxisParallelLine params g ℓt.1) ℓt.2 ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓt.1).poly then
              (1 : Error)
            else 0) *
              ev ψbi (opTensor
                ((strategy.axisParallelMeasurement ℓt.1).toSubMeas.outcome f)
                (G.outcome g)))
      = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ => avgOver (uniformDistribution (Fq params))
            (fun t =>
              ∑ f : AxisLinePolynomial params,
                (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                    f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                  (1 : Error)
                else 0) *
                  ev ψbi (opTensor
                    ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                    (G.outcome g)))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelLine params) (β := Fq params)
            (f := fun ℓ t =>
              ∑ f : AxisLinePolynomial params,
                (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                    f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                  (1 : Error)
                else 0) *
                  ev ψbi (opTensor
                    ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                    (G.outcome g)))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              avgOver (uniformDistribution (Fq params))
                (fun t =>
                  (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                      f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                    (1 : Error)
                  else 0) *
                    ev ψbi (opTensor
                      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                      (G.outcome g)))) := by
          apply avgOver_congr
          intro ℓ
          exact avgOver_sum (uniformDistribution (Fq params))
            (fun t f =>
              (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                  f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                (1 : Error)
              else 0) *
                ev ψbi (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g)))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              avgOver (uniformDistribution (Fq params))
                (fun t =>
                  if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                      f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                    (1 : Error)
                  else 0) *
                ev ψbi (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g))) := by
          apply avgOver_congr
          intro ℓ
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [avgOver_mul_const]

/-- The incident-question collision residual is exactly the uniform line/parameter
seed expansion from `expansion.tex`, lines 286--288.

The proof reindexes the axis-parallel line-test distribution by `(ℓ,t)` with
sampled point `u = ℓ(t)`, then expands the `ProjMeas.postprocess` fiber for the
collision event `f(t) = g|_ℓ(t)` and `f ≠ g|_ℓ`. -/
lemma generalizeBCollisionResidual_eq_seedCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g =
      generalizeBSeedCollisionExpansion params strategy strategy.state G g := by
  classical
  unfold generalizeBCollisionResidual generalizeBSeedCollisionExpansion
  rw [avgOver_axisParallelLineQuestionDistribution]
  apply avgOver_congr
  intro ℓt
  cases ℓt with
  | mk ℓ t =>
      exact generalizeBCollisionSeed_integrand params strategy strategy.state G g ℓ t

/-- The explicit line/parameter collision expansion is bounded by `m*d/q`.

This proves the Schwartz--Zippel and normalization parts of the residual estimate
from `expansion.tex`, lines 286--288.  The preceding
`generalizeBCollisionResidual_eq_seedCollisionExpansion` theorem supplies the
incident-question/postprocess identity needed to apply this bound to the original
collision residual. -/
lemma generalizeBLineCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBLineCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  classical
  let δ := generalizeBError params
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, generalizeBError]
    positivity
  unfold generalizeBLineCollisionExpansion
  calc
    avgOver (uniformDistribution (AxisParallelLine params))
      (fun ℓ =>
        ∑ f : AxisLinePolynomial params,
          avgOver (uniformDistribution (Fq params))
            (fun t =>
              if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                  f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                (1 : Error)
              else 0) *
            ev strategy.state (opTensor
              ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
              (G.outcome g)))
      ≤ avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              δ * ev strategy.state (opTensor
                ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                (G.outcome g))) := by
            refine avgOver_mono _ _ _ ?_
            intro ℓ
            refine Finset.sum_le_sum ?_
            intro f _
            exact mul_le_mul_of_nonneg_right
              (by simpa [δ] using generalizeBLineCollisionCoefficient_le params g ℓ f)
              (generalizeBLineCollisionTensorMass_nonneg params strategy G g ℓ f)
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ => δ * ∑ f : AxisLinePolynomial params,
            ev strategy.state (opTensor
              ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
              (G.outcome g))) := by
            apply avgOver_congr
            intro ℓ
            rw [Finset.mul_sum]
    _ ≤ δ := by
            exact avgOver_uniform_le_const
              (fun ℓ : AxisParallelLine params => δ *
                ∑ f : AxisLinePolynomial params,
                  ev strategy.state (opTensor
                    ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                    (G.outcome g)))
              δ
              (fun ℓ => by
                simpa using mul_le_mul_of_nonneg_left
                  (generalizeBLineCollisionTensorMass_sum_le_one params strategy G g ℓ)
                  hδ_nonneg)
    _ = generalizeBError params := rfl

/-- The uniform line/parameter seed collision expansion is bounded by `m*d/q`.

The proof first commutes the finite seed average into the coefficient-weighted
line expansion, then applies the Schwartz--Zippel coefficient bound and tensor
normalization estimate above. -/
lemma generalizeBSeedCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion]
  exact generalizeBLineCollisionExpansion_le_error params strategy G g

/-- The pointwise collision residual in `lem:generalize-b` is bounded by `m*d/q`.

This combines the incident-question reindexing with the seed/line expansion,
Schwartz--Zippel coefficient bound, and submeasurement-normalization estimate
from `expansion.tex`, lines 281--288. -/
lemma generalizeBCollisionResidual_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBCollisionResidual_eq_seedCollisionExpansion]
  exact generalizeBSeedCollisionExpansion_le_error params strategy G g

/-- Pointwise Schwartz--Zippel bound for the strategy-state form of
`lem:generalize-b`.

This is the paper's estimate at `expansion.tex`, lines 281--288, after the
projective expansion converts the squared norm into the collision residual. -/
lemma generalizeBPointwiseSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBDeviationAtPolynomial params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBDeviationAtPolynomial_eq_collisionResidual]
  exact generalizeBCollisionResidual_le_error params strategy G g

/-- `lem:generalize-b` for the strategy state, with the pointwise
Schwartz--Zippel estimate discharged internally.  The good-strategy hypothesis is
kept in the statement to match the paper context of `expansion.tex`,
lines 271--288, although the algebraic Schwartz--Zippel proof itself does not
use `ε`, `δ`, or `γ`. -/
lemma generalizeBFromSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι) :
    GeneralizeBStatement params strategy strategy.state G := by
  refine generalizeB_of_pointwise params strategy G strategy.state ?_
  intro g
  exact generalizeBPointwiseSchwartzZippel params strategy G g

end

end MIPStarRE.LDT.GlobalVariance

end LIDT


