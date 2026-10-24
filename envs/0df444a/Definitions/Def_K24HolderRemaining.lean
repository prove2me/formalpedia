-- Prove2me | Definitions.Def_K24HolderRemaining
-- name    : K24HolderRemaining
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T20:24:58.889916+00:00
-- url     : https://prove2.me/theorems/f4287a61-d761-4ee3-bef4-a175ea4c3c41
-- title:
--   K24: remaining natural and shifted Holder analytic obligations
-- statement:
--   # Transparent remaining Holder obligations
--
--   HolderNaturalRemaining and HolderShiftedRemaining retain literal fields of
--   the immutable HolderNaturalAnalyticCore and HolderShiftedAnalyticCore. The
--   following fields are omitted because the reconstruction supplies actual proofs:
--
--   | Original bundle | Omitted fields |
--   | --- | --- |
--   | Natural | projections; tensor_domain_banach; tensor_target_banach; tensor_perp_domain_banach; tensor_perp_target_banach; vector_domain_banach; vector_target_banach; positive_neighborhood; center_comparison |
--   | Shifted | projections; domain_banach; target_banach |
--
--   Every other field is copied with exactly its original type, including all
--   actual operator mapping, restricted linearity and boundedness obligations.
--   The original explicit parameters are retained, including H.
--
--   UniformHolderNaturalRemaining and UniformHolderShiftedRemaining copy the
--   original uniform propositions, replacing only the names of the conclusion
--   bundles. Bounds, hypotheses, quantifier order, positivity conditions, exponent,
--   orders and the number and dependencies of uniform constants are identical.
--   The existing UniformSobolevAnalyticCore is reused literally; no Sobolev
--   replacement or weakened Sobolev conclusion is defined.
--
--   These are transparent propositions describing unresolved conclusions, not
--   assertions that those conclusions have been proved. The intended three
--   substantial children are the two remaining uniform Holder statements and the
--   original uniform Sobolev analytic core. The checked conversion from their
--   conjunction restores the original AnalyticCoreStatement.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — transparent residual interface for the original K24 analytic-core theorem 3db797ab-2b53-4cda-b318-e4780235e38c. Retained fields, all hypotheses and uniform constant quantifier order are copied unchanged; Sobolev core is reused literally. This definition proves no residual obligation.

import Definitions.Def_K24AnalyticCore

/- Transparent remaining Holder obligations. Every retained field is copied
literally from the immutable analytic core. Only proved foundational fields
are omitted; the uniform numerical constants and their quantifier order are
unchanged. UniformSobolevAnalyticCore is reused without any modification. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
structure HolderNaturalRemaining (C : BoundedLocalCover M) (alpha H CT CV : ℝ≥0)
    (rho : CircleAction M) (lam : ℝ) (ghat z g : RawCov2 M) : Prop where
  exact_identities : ExactChangeOfSliceConclusions C alpha rho lam ghat z g
  bianchi_regularity : ∀ u : RawCov2 M, C.Cov2Holder 2 alpha u →
    C.CovectorHolder 1 alpha (bianchi ghat u) ∧
    C.CovectorHolder 1 alpha (bianchi z u) ∧
    CovectorHaarIntegrable rho (bianchi ghat u) ∧ CovectorHaarIntegrable rho (bianchi z u)
  vector_regularity : ∀ Y : RawVector M, C.VectorHolder 2 alpha Y →
    C.Cov2Holder 1 alpha (lieTensor Y g) ∧
    C.CovectorHolder 0 alpha (vectorOperator ghat g Y) ∧
    C.CovectorHolder 0 alpha (vectorOperator z z Y) ∧
    CovectorHaarIntegrable rho (vectorOperator ghat g Y) ∧
    CovectorHaarIntegrable rho (vectorOperator z z Y)
  defect_regularity : ∀ u ∈ tensorHolderSpace C 2 alpha,
    C.Cov2Holder 0 alpha (tensorDefect ghat z u)
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
  symbol_estimate : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
    ∀ (xi : Fin 4 → ℝ) (a : Mat4),
      metricTensorPointNorm z c x (tensorDefectPrincipalSymbol ghat z c x xi a) ≤
        (CT : ℝ) * metricTensorPointNorm z c x (cov2InChart (ghat - z) c x) *
          (metricCovectorPointNorm z c x xi) ^ 2 * metricTensorPointNorm z c x a
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
  vector_operator :
    Set.MapsTo (projectedVectorOperator rho ghat g)
      (vectorHolderPerp C 2 alpha rho) (covectorHolderPerp C 0 alpha rho) ∧
    SectionLinearOn (vectorHolderPerp C 2 alpha rho) (projectedVectorOperator rho ghat g) ∧
    SectionBoundedOn (vectorHolderPerp C 2 alpha rho)
      (C.vectorENorm 2 alpha) (C.covectorENorm 0 alpha) (projectedVectorOperator rho ghat g)

structure HolderShiftedRemaining (C : BoundedLocalCover M) (alpha H CV : ℝ≥0)
    (rho : CircleAction M) (ghat z g : RawCov2 M) : Prop where
  vector_regularity : ∀ Y : RawVector M, C.VectorHolder 3 alpha Y →
    C.Cov2Holder 2 alpha (lieTensor Y g) ∧
    C.CovectorHolder 1 alpha (vectorOperator ghat g Y) ∧
    C.CovectorHolder 1 alpha (vectorOperator z z Y) ∧
    CovectorHaarIntegrable rho (vectorOperator ghat g Y) ∧
    CovectorHaarIntegrable rho (vectorOperator z z Y)
  center_estimate : ∀ Y : RawVector M, C.VectorHolder 3 alpha Y →
    C.covectorENorm 1 alpha
        (projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y) ≤
      (CV : ℝ≥0∞) * C.cov2ENorm 3 alpha (ghat - z) * C.vectorENorm 3 alpha Y
  actual_estimate : ∀ Y : RawVector M, C.VectorHolder 3 alpha Y →
    C.covectorENorm 1 alpha
        (projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y) ≤
      (CV : ℝ≥0∞) * (C.cov2ENorm 3 alpha (ghat - z) + C.cov2ENorm 3 alpha (g - z)) *
        C.vectorENorm 3 alpha Y
  vector_operator :
    Set.MapsTo (projectedVectorOperator rho ghat g)
      (vectorHolderPerp C 3 alpha rho) (covectorHolderPerp C 1 alpha rho) ∧
    SectionLinearOn (vectorHolderPerp C 3 alpha rho) (projectedVectorOperator rho ghat g) ∧
    SectionBoundedOn (vectorHolderPerp C 3 alpha rho)
      (C.vectorENorm 3 alpha) (C.covectorENorm 1 alpha) (projectedVectorOperator rho ghat g)

universe u

def UniformHolderNaturalRemaining : Prop :=
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
        HolderNaturalRemaining C metricBounds.exponent.value H CT CV rho lam ghat z g

def UniformHolderShiftedRemaining : Prop :=
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
        HolderShiftedRemaining C metricBounds.exponent.value H CV rho ghat z g

end K24.Global


