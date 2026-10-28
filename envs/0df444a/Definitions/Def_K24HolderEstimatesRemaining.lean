-- Prove2me | Definitions.Def_K24HolderEstimatesRemaining
-- name    : K24HolderEstimatesRemaining
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-26T05:08:32.188753+00:00
-- url     : https://prove2.me/theorems/439451b7-8ace-44d3-8e08-8c040b7b929b
-- title:
--   K24 Holder estimates remaining after actual regularity and vector operators
-- statement:
--   This transparent package records the unresolved natural and shifted Holder obligations after the original regularity, vector-operator, and principal-symbol fields are supplied by separate proved results. It asserts no proof of the retained goals.
--
--   The natural bundle retains seven literal fields: exact geometric change-of-slice identities; the fixed and reanchored full Frechet derivative assertions for the actual partial gauge; the numerical tensor-defect estimate; both center and actual-metric vector difference estimates; and the actual tensor-operator mapping, linearity and finite boundedness. The shifted bundle retains precisely its center and actual-metric vector difference estimates.
--
--   The uniform propositions keep every original hypothesis, actual metric, norm, exponent, order and quantifier: numerical cover and metric data and the action bound are fixed before the positive CT/CV constants, and those constants then work for all admissible manifolds, covers, actions, centers, references, actual metrics and tested sections. The natural metric order remains at least two; the shifted branch has the original order-three hypothesis. Invariance is imposed only where it was imposed originally.
--
--   A separately checked reconstruction joins the natural tensor-estimate constant with the independently uniform symbol constant by taking their maximum. It then restores the five removed natural fields; the shifted reconstruction restores its two removed fields. These are conditional reductions, and the seven/two retained obligations remain open until actually proved. The Sobolev branch is unaffected.
-- source:
--   Literal retained fields and quantifiers from Definitions.Def_K24HolderRemaining, existing natural target https://prove2.me/theorems/aef928c5-5b96-4abc-bee6-ac8ce63825b8 and shifted target https://prove2.me/theorems/0bb2ce06-572d-4846-8b63-f3baab196544 . Original full K24 source: https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md .

import Definitions.Def_K24HolderRemaining

/- Remaining original Holder estimates and nonlinear/tensor obligations.
Retained fields are literal copies of Def_K24HolderRemaining. Removed fields
are supplied separately by proved regularity/operator/symbol results. This
module defines unresolved goals; it does not assert their completion. The
uniform numerical constants and original outer quantifiers remain unchanged. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
structure HolderNaturalEstimatesRemaining (C : BoundedLocalCover M) (alpha H CT CV : ℝ≥0)
    (rho : CircleAction M) (lam : ℝ) (ghat z g : RawCov2 M) : Prop where
  exact_identities : ExactChangeOfSliceConclusions C alpha rho lam ghat z g
  fixed_frechet : HasSectionFrechetDerivative (tensorHolderSpace C 2 alpha)
    (positiveHolderMetrics C 2 alpha) (tensorHolderSpace C 0 alpha)
    (C.cov2ENorm 2 alpha) (C.cov2ENorm 0 alpha)
    (partialGauge rho lam ghat) (partialGaugeVariation rho lam ghat z) z
  reanchored_frechet : HasSectionFrechetDerivative (tensorHolderSpace C 2 alpha)
    (positiveHolderMetrics C 2 alpha) (tensorHolderSpace C 0 alpha)
    (C.cov2ENorm 2 alpha) (C.cov2ENorm 0 alpha)
    (partialGauge rho lam z) (partialGaugeVariation rho lam z z) z
  tensor_estimate : ∀ u ∈ tensorHolderSpace C 2 alpha,
    C.cov2ENorm 0 alpha (tensorDefect ghat z u) ≤
      (CT : ℝ≥0∞) * C.cov2ENorm 2 alpha (ghat - z) * C.cov2ENorm 2 alpha u
  vector_center_estimate : ∀ Y : RawVector M, C.VectorHolder 2 alpha Y →
    C.covectorENorm 0 alpha
        (projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y) ≤
      (CV : ℝ≥0∞) * C.cov2ENorm 2 alpha (ghat - z) * C.vectorENorm 2 alpha Y
  vector_actual_estimate : ∀ Y : RawVector M, C.VectorHolder 2 alpha Y →
    C.covectorENorm 0 alpha
        (projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y) ≤
      (CV : ℝ≥0∞) * (C.cov2ENorm 2 alpha (ghat - z) + C.cov2ENorm 2 alpha (g - z)) *
        C.vectorENorm 2 alpha Y
  tensor_operator :
    Set.MapsTo (projectedTensorOperator rho lam ghat z)
      (tensorHolderPerp C 2 alpha rho) (tensorHolderPerp C 0 alpha rho) ∧
    SectionLinearOn (tensorHolderPerp C 2 alpha rho) (projectedTensorOperator rho lam ghat z) ∧
    SectionBoundedOn (tensorHolderPerp C 2 alpha rho)
      (C.cov2ENorm 2 alpha) (C.cov2ENorm 0 alpha) (projectedTensorOperator rho lam ghat z)

structure HolderShiftedEstimatesRemaining (C : BoundedLocalCover M) (alpha H CV : ℝ≥0)
    (rho : CircleAction M) (ghat z g : RawCov2 M) : Prop where
  center_estimate : ∀ Y : RawVector M, C.VectorHolder 3 alpha Y →
    C.covectorENorm 1 alpha
        (projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y) ≤
      (CV : ℝ≥0∞) * C.cov2ENorm 3 alpha (ghat - z) * C.vectorENorm 3 alpha Y
  actual_estimate : ∀ Y : RawVector M, C.VectorHolder 3 alpha Y →
    C.covectorENorm 1 alpha
        (projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y) ≤
      (CV : ℝ≥0∞) * (C.cov2ENorm 3 alpha (ghat - z) + C.cov2ENorm 3 alpha (g - z)) *
        C.vectorENorm 3 alpha Y

universe u

def UniformHolderNaturalEstimatesRemaining : Prop :=
  ∀ (coverBounds : CoverNumerics) (metricBounds : MetricCoefficientNumerics)
    (H : ℝ≥0), 1 ≤ H →
    ∃ CT CV : ℝ≥0, 0 < CT ∧ 0 < CV ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
      ∀ C : BoundedLocalCover M, C.numerics = coverBounds →
      ∀ rho : CircleAction M,
        HolderActionControl C metricBounds.exponent.value H 2 rho →
      ∀ (lam : ℝ) (ghat z g : RawCov2 M),
        MetricAdmissible C metricBounds ghat →
        MetricAdmissible C metricBounds z →
        MetricAdmissible C metricBounds g →
        IsInvariantCov2 rho ghat → IsInvariantCov2 rho z →
        HolderNaturalEstimatesRemaining C metricBounds.exponent.value H CT CV rho lam ghat z g

def UniformHolderShiftedEstimatesRemaining : Prop :=
  ∀ (coverBounds : CoverNumerics) (metricBounds : MetricCoefficientNumerics),
    3 ≤ metricBounds.order →
    ∀ H : ℝ≥0, 1 ≤ H →
    ∃ CV : ℝ≥0, 0 < CV ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
      ∀ C : BoundedLocalCover M, C.numerics = coverBounds →
      ∀ rho : CircleAction M,
        HolderActionControl C metricBounds.exponent.value H 3 rho →
      ∀ ghat z g : RawCov2 M,
        MetricAdmissible C metricBounds ghat →
        MetricAdmissible C metricBounds z →
        MetricAdmissible C metricBounds g →
        IsInvariantCov2 rho ghat → IsInvariantCov2 rho z →
        HolderShiftedEstimatesRemaining C metricBounds.exponent.value H CV rho ghat z g

end K24.Global


