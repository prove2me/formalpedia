-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:41:27.487766+00:00
-- url     : https://prove2.me/theorems/0de90dd0-77a7-430e-aea2-ccbf4334c3fc
-- title:
--   LIDT definitions: LDT / GlobalVariance / Defs / Families
-- statement:
--   This bundle defines the operator families and sampled questions used in the global-variance comparison. The families expand the generalize-b deviation and its collision residual into the line and parameter averages needed by the variance proof.
--
--   Principal definitions:
--   - `generalizeBDeviationAtPolynomial`: the squared deviation quantity for a fixed polynomial outcome.
--   - `generalizeBDeviation`: the polynomial-averaged generalize-b deviation.
--   - `generalizeBCollisionResidual`: the residual created by expanding the line measurement and moving a polynomial weight between square-root and full operators.
--   - `generalizeBSeedCollisionExpansion`: the collision residual expanded over uniform line and parameter seeds.
--   - `generalizeBLineCollisionExpansion`: the explicit line and parameter expansion of the collision residual.
--   - `generalizeBLeftFamily`: the aggregated left operator family in the generalize-b comparison.
--   - `generalizeBRightFamily`: the aggregated right operator family in the generalize-b comparison.
--   - `localVarianceLeftFamily`: the aggregated family containing a point answer operator and a square-root polynomial weight.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Defs/Families.lean#L29-L387

-- Generated from MIPStarRE/LDT/GlobalVariance/Defs/Families.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

/-!
# Section 8 global variance: operator families

Positivity and normalization lemmas for the point-conditioned outcome
operator families used to build the global-variance comparisons.

## References

- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-- `CFC.sqrt (G.outcome g) ≤ 1` when `G` is a submeasurement.
Proved via the NNReal CFC spectrum API: `G.outcome g ≤ 1` means all
spectral values satisfy `λ ≤ 1`, so `√λ ≤ 1` as well. -/
private lemma cfc_sqrt_outcome_le_one (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    CFC.sqrt (G.outcome g) ≤ 1 := by
  have hspec_le : ∀ x, x ∈ spectrum NNReal (G.outcome g) → x ≤ 1 := by
    have hle : G.outcome g ≤ 1 := G.outcome_le_one g
    rw [← cfc_id' NNReal (G.outcome g) (ha := G.outcome_pos g),
      ← cfc_const_one (R := NNReal) (G.outcome g) (ha := G.outcome_pos g),
      cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg (G.outcome_pos g))
        (ha := G.outcome_pos g)] at hle
    exact hle
  rw [CFC.sqrt_eq_cfc, ← cfc_const_one (R := NNReal) (G.outcome g) (ha := G.outcome_pos g),
    cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg (G.outcome_pos g))
      (ha := G.outcome_pos g)]
  intro x hx
  -- √x ≤ 1 follows from x ≤ 1 for NNReal (NNReal.sqrt_le_one)
  simpa using hspec_le x hx

private theorem weightedPolynomialOperator_pos (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    {A : MIPStarRE.Quantum.Op ι} (hA : 0 ≤ A) :
    0 ≤ opTensor A (polynomialWeightSqrtOperator params G g) := by
  simpa [polynomialWeightSqrtOperator] using
    (opTensor_nonneg hA (CFC.sqrt_nonneg (G.outcome g)))

private theorem weightedPolynomialOperator_le_one (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    {A : MIPStarRE.Quantum.Op ι}
    (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    opTensor A (polynomialWeightSqrtOperator params G g) ≤ 1 := by
  calc
    opTensor A (polynomialWeightSqrtOperator params G g)
      ≤ leftTensor (ι₂ := ι) A :=
        opTensor_le_leftTensor hA_pos (cfc_sqrt_outcome_le_one params G g)
    _ ≤ 1 := leftTensor_le_one hA_le_one

private theorem weightedPointConditionedOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    0 ≤ weightedPointConditionedOperatorAtPolynomial params strategy G g u := by
  simpa [weightedPointConditionedOperatorAtPolynomial] using
    (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
      (A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
      (by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          (strategy.pointMeasurement u).outcome_pos (g u)))

private theorem weightedPointConditionedOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    weightedPointConditionedOperatorAtPolynomial params strategy G g u ≤ 1 := by
  have hA_le_one :
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u ≤ 1 := by
    simpa [pointConditionedOutcomeOperatorAtPolynomial] using
      Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u)
  simpa [weightedPointConditionedOperatorAtPolynomial] using
    (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G) (g := g)
      (A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
      (by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          (strategy.pointMeasurement u).outcome_pos (g u))
      hA_le_one)

/-- The squared norm expression controlled by `lem:generalize-b` for a fixed `g`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def generalizeBDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
               weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
      ev ψbi (Dᴴ * D))

/-- The polynomial-averaged deviation controlled by `lem:generalize-b`. -/
noncomputable def generalizeBDeviation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)

/-- The line-collision residual obtained after expanding the projective line
measurement in `lem:generalize-b` and moving the polynomial weight from
`(G_g)^{1/2}` to `G_g`.  The remaining unproved analytic step is to bound this
quantity by Schwartz--Zippel and the submeasurement property of `G`.

Paper origin: `references/ldt-paper/expansion.tex:273-288`
(`\label{lem:generalize-b}`). -/
noncomputable def generalizeBCollisionResidual (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      ev ψbi (opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g qu)
        (G.outcome g)))

/-- Uniform line/parameter seed expansion of the `lem:generalize-b` collision residual.

This is the paper's `expansion.tex`, lines 286--288, after replacing an
incident line question `(ℓ,u)` by a line `ℓ` and affine parameter `t` with
`u = ℓ(t)`, but before commuting the finite average over `t` past the finite
sum over line answers `f`.  The equality from the original collision residual to
this seed expansion is proved in
`generalizeBCollisionResidual_eq_seedCollisionExpansion`. -/
noncomputable def generalizeBSeedCollisionExpansion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
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

/-- Explicit line/parameter expansion of the `lem:generalize-b` collision residual.

This is the commuted finite-sum form of `generalizeBSeedCollisionExpansion`: for
fixed `ℓ` and `f`, the coefficient is the fraction of parameters where the line
answer `f` both collides with `g|_ℓ` at `t` and is not equal to `g|_ℓ`. -/
noncomputable def generalizeBLineCollisionExpansion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (uniformDistribution (AxisParallelLine params))
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
            (G.outcome g)))

/-- Aggregated family for the left-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (Polynomial params)) F
        (fun g => by
          change
            0 ≤ weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          simpa [weightedGeneralizeBLeftOperatorAtPolynomial] using
            (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
              (A := generalizeBLeftOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBLeftOperatorAtPolynomial] using
                  (generalizeBLeftEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ())))))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => by
          change weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu ≤ 1
          simpa [weightedGeneralizeBLeftOperatorAtPolynomial] using
            (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G)
              (g := g)
              (A := generalizeBLeftOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBLeftOperatorAtPolynomial] using
                  (generalizeBLeftEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ()))
              (by
                simpa [generalizeBLeftOperatorAtPolynomial] using
                  SubMeas.outcome_le_one
                    (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu)
                    (some ())))))

/-- Aggregated family for the right-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (Polynomial params)) F
        (fun g => by
          change
            0 ≤ weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          simpa [weightedGeneralizeBRightOperatorAtPolynomial] using
            (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
              (A := generalizeBRightOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBRightOperatorAtPolynomial] using
                  (generalizeBRightEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ())))))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => by
          change weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu ≤ 1
          simpa [weightedGeneralizeBRightOperatorAtPolynomial] using
            (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G)
              (g := g)
              (A := generalizeBRightOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBRightOperatorAtPolynomial] using
                  (generalizeBRightEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ()))
              (by
                simpa [generalizeBRightOperatorAtPolynomial] using
                  SubMeas.outcome_le_one
                    (generalizeBRightEventSubMeasAtPolynomial params strategy g qu)
                    (some ())))))

/-- Aggregated family for `A^u_[g(u)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (by
        exact averageOperatorOverDistribution_nonneg
          (uniformDistribution (Polynomial params)) F
          (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.1))
      (by
        exact averageOperatorOverDistribution_uniform_le_one F
          (fun g =>
            weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.1))

/-- Aggregated family for `A^v_[g(v)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (by
        exact averageOperatorOverDistribution_nonneg
          (uniformDistribution (Polynomial params)) F
          (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.2))
      (by
        exact averageOperatorOverDistribution_uniform_le_one F
          (fun g =>
            weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.2))

/-- The same weighted operator on the first independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceLeftFamily params strategy G

/-- The same weighted operator on the second independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceRightFamily params strategy G

/-- The edgewise squared norm expression in `lem:local-variance-of-points`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def localVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (rerandomizeCoord params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      ev ψbi (Dᴴ * D))

/-- The independently sampled squared norm expression in `lem:global-variance-of-points`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def globalVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (independentPointPair params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      ev ψbi (Dᴴ * D))



/-- The displayed error term in `lem:generalize-b`. -/
noncomputable def generalizeBError (params : Parameters) : Error :=
  ((params.m : Error) * (params.d : Error)) / (params.q : Error)

/-- The post-triangle-inequality error term for the six-step transport in
`lem:local-variance-of-points`.

The six comparisons at `references/ldt-paper/expansion.tex`, lines 305--311
have errors `2δ`, `2ε`, `md/q`, `md/q`, `2ε`, and `2δ`, whose sum is
`4ε + 4δ + 2md/q`.  The paper then applies
`prop:triangle-inequality-for-approx_delta` (`preliminaries.tex:622--642`) with
`k = 6`, yielding `6 * (4ε + 4δ + 2md/q)`.  This is the genuine residual that
the six-step chain is expected to prove before it is absorbed by the displayed
`24(ε + δ + md/q)` slack. -/
noncomputable def localVarianceTransportChainError (params : Parameters)
    (eps delta : Error) : Error :=
  6 * (4 * eps + 4 * delta + 2 * generalizeBError params)

/-- The displayed error term in `lem:local-variance-of-points`. -/
noncomputable def localVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (eps + delta + generalizeBError params)

/-- The displayed error term in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (params.m : Error) * (eps + delta + generalizeBError params)

end MIPStarRE.LDT.GlobalVariance

end

end LIDT


