-- Prove2me | Definitions.Def_K24AnalyticCore
-- name    : K24AnalyticCore
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T18:58:40.63299+00:00
-- url     : https://prove2.me/theorems/6e2f7d75-89ec-404a-a6f9-d2cdffb046e6
-- title:
--   K24 remaining analytic core after exact section inverse transfer
-- statement:
--   This package defines the remaining geometric and analytic obligations for a proof of the complete conditional K24 theorem. It introduces three transparent conclusion bundles and their uniform statements in the natural Holder, shifted Holder and real-order Sobolev scales.
--
--   Every original non-inverse conclusion is retained: projection laws, exact differential identities, regularity and integrability, actual section-space Banach laws, positive metric neighborhoods, Frechet differentiation, uniform difference and symbol estimates, and center comparison. The original quantifier order is unchanged: numerical geometry/action bounds precede the uniform constants, which then apply to all admissible manifolds, covers, actions and metrics. The Sobolev statement still covers every real $s>4$.
--
--   Four conditional inverse-transfer clauses are removed from these residual bundles. Instead, each bundle explicitly requests that the same actual fixed-reference projected operator maps the specified perpendicular section domain to the specified target and is linear and bounded there. These are unproved conclusions under the unchanged geometric hypotheses. Their finite bounds may depend on the fixed data, including $\lambda$; no new uniform bound by the difference-estimate constants is imposed.
--
--   The conjunction of these three residual uniform statements is `AnalyticCoreStatement`. It is a sufficient residual strengthening, not an asserted equivalence with the original non-inverse clauses. It makes no claim that these obligations are proved. Together with the separate original geometric torus sharpness statement, the proved section Neumann theorem reconstructs the full K24 statement. No target conclusion is inserted as a hypothesis of the original theorem.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §§2–5 and §8; operator pairs in §3 equations (3.8)–(3.9), §5 equations (5.3)–(5.5); original FullK24Statement definition package https://prove2.me/theorems/9140e2e8-3049-4225-86fe-cfe1a8c49825 .

import Definitions.Def_K24GlobalStatement

/-!
# Remaining analytic core for K24

These transparent propositions retain every original geometric and analytic
conclusion except the four conditional inverse-transfer fields. In their place
are ordinary mapping, restricted linearity, and boundedness obligations for the
same actual projected operators. These obligations remain unproved conclusions
under the original geometric hypotheses; they are never assumed for FullK24.
The separately unresolved literal flat-torus sharpness statement is omitted.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

structure HolderNaturalAnalyticCore (C : BoundedLocalCover M) (alpha H CT CV : ℝ≥0)
    (rho : CircleAction M) (lam : ℝ) (ghat z g : RawCov2 M) : Prop where
  projections : HolderProjectionConclusions C alpha H 2 rho
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
  tensor_domain_banach : SectionBanachSpace (tensorHolderSpace C 2 alpha) (C.cov2ENorm 2 alpha)
  tensor_target_banach : SectionBanachSpace (tensorHolderSpace C 0 alpha) (C.cov2ENorm 0 alpha)
  tensor_perp_domain_banach : SectionBanachSpace (tensorHolderPerp C 2 alpha rho) (C.cov2ENorm 2 alpha)
  tensor_perp_target_banach : SectionBanachSpace (tensorHolderPerp C 0 alpha rho) (C.cov2ENorm 0 alpha)
  vector_domain_banach : SectionBanachSpace (vectorHolderPerp C 2 alpha rho) (C.vectorENorm 2 alpha)
  vector_target_banach : SectionBanachSpace (covectorHolderPerp C 0 alpha rho) (C.covectorENorm 0 alpha)
  positive_neighborhood : SectionNeighborhood (tensorHolderSpace C 2 alpha)
    (positiveHolderMetrics C 2 alpha) (C.cov2ENorm 2 alpha) z
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
  center_comparison : ∀ q ∈ tensorHolderSpace C 2 alpha,
    C.cov2ENorm 2 alpha (cov2Pi0 rho (q - ghat)) ≤
      (H : ℝ≥0∞) * C.cov2ENorm 2 alpha (q - ghat)
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

structure HolderShiftedAnalyticCore (C : BoundedLocalCover M) (alpha H CV : ℝ≥0)
    (rho : CircleAction M) (ghat z g : RawCov2 M) : Prop where
  projections : HolderProjectionConclusions C alpha H 3 rho
  domain_banach : SectionBanachSpace (vectorHolderPerp C 3 alpha rho) (C.vectorENorm 3 alpha)
  target_banach : SectionBanachSpace (covectorHolderPerp C 1 alpha rho) (C.covectorENorm 1 alpha)
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

structure SobolevAnalyticCore {C : BoundedLocalCover M} (P : SobolevPartition C)
    (s : ℝ) (H CS : ℝ≥0) (rho : CircleAction M) (lam : ℝ)
    (ghat z : RawCov2 M) : Prop where
  bianchi_regularity : ∀ u ∈ tensorSobolevSpace P 2 s,
    P.CovectorSobolev 1 (s - 1) (bianchi ghat u) ∧
    P.CovectorSobolev 1 (s - 1) (bianchi z u) ∧
    CovectorHaarIntegrable rho (bianchi ghat u) ∧ CovectorHaarIntegrable rho (bianchi z u)
  defect_regularity : ∀ u ∈ tensorSobolevSpace P 2 s,
    P.Cov2Sobolev 0 (s - 2) (tensorDefect ghat z u)
  domain_banach : SectionBanachSpace (tensorSobolevSpace P 2 s) (P.cov2SobolevENorm s)
  target_banach : SectionBanachSpace (tensorSobolevSpace P 0 (s - 2)) (P.cov2SobolevENorm (s - 2))
  perp_domain_banach : SectionBanachSpace (tensorSobolevPerp P 2 s rho) (P.cov2SobolevENorm s)
  perp_target_banach : SectionBanachSpace (tensorSobolevPerp P 0 (s - 2) rho)
    (P.cov2SobolevENorm (s - 2))
  tensor_projection : ∀ j ≤ 2, ∀ u : RawCov2 M, P.Cov2Sobolev (2 - j) (s - j) u →
    Cov2HaarIntegrable rho u ∧
    P.Cov2Sobolev (2 - j) (s - j) (cov2Pi0 rho u) ∧
    P.Cov2Sobolev (2 - j) (s - j) (cov2PiPerp rho u) ∧
    cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
    IsNonzeroCov2 rho (cov2PiPerp rho u) ∧
    P.cov2SobolevENorm (s - j) (cov2Pi0 rho u) ≤ (H : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u ∧
    P.cov2SobolevENorm (s - j) (cov2PiPerp rho u) ≤
      ((1 + H : ℝ≥0) : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u
  covector_projection : ∀ j ≤ 2, ∀ eta : RawCovector M,
    P.CovectorSobolev (2 - j) (s - j) eta →
    CovectorHaarIntegrable rho eta ∧
    P.CovectorSobolev (2 - j) (s - j) (covectorPi0 rho eta) ∧
    P.CovectorSobolev (2 - j) (s - j) (covectorPiPerp rho eta) ∧
    IsNonzeroCovector rho (covectorPiPerp rho eta) ∧
    P.covectorSobolevENorm (s - j) (covectorPi0 rho eta) ≤
      (H : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta ∧
    P.covectorSobolevENorm (s - j) (covectorPiPerp rho eta) ≤
      ((1 + H : ℝ≥0) : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta
  positive_neighborhood : SectionNeighborhood (tensorSobolevSpace P 2 s)
    (positiveSobolevMetrics P s) (P.cov2SobolevENorm s) z
  fixed_frechet : HasSectionFrechetDerivative (tensorSobolevSpace P 2 s)
    (positiveSobolevMetrics P s) (tensorSobolevSpace P 0 (s - 2))
    (P.cov2SobolevENorm s) (P.cov2SobolevENorm (s - 2))
    (partialGauge rho lam ghat) (partialGaugeVariation rho lam ghat z) z
  reanchored_frechet : HasSectionFrechetDerivative (tensorSobolevSpace P 2 s)
    (positiveSobolevMetrics P s) (tensorSobolevSpace P 0 (s - 2))
    (P.cov2SobolevENorm s) (P.cov2SobolevENorm (s - 2))
    (partialGauge rho lam z) (partialGaugeVariation rho lam z z) z
  cancellation : covectorPiPerp rho (bianchi ghat (z - ghat)) = 0
  product_rule : ∀ u ∈ tensorSobolevSpace P 2 s,
    partialGaugeVariation rho lam ghat z u = partialGaugeProductRule rho lam ghat z u
  dangerous_term_zero : ∀ u ∈ tensorSobolevSpace P 2 s,
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) = 0
  tensor_difference : ∀ u ∈ tensorSobolevPerp P 2 s rho,
    projectedTensorOperator rho lam ghat z u - projectedTensorOperator rho lam z z u =
      tensorDefect ghat z u
  tensor_estimate : ∀ u ∈ tensorSobolevSpace P 2 s,
    P.cov2SobolevENorm (s - 2) (tensorDefect ghat z u) ≤
      (CS : ℝ≥0∞) * P.cov2SobolevENorm s (ghat - z) * P.cov2SobolevENorm s u
  tensor_operator :
    Set.MapsTo (projectedTensorOperator rho lam ghat z)
      (tensorSobolevPerp P 2 s rho) (tensorSobolevPerp P 0 (s - 2) rho) ∧
    SectionLinearOn (tensorSobolevPerp P 2 s rho) (projectedTensorOperator rho lam ghat z) ∧
    SectionBoundedOn (tensorSobolevPerp P 2 s rho)
      (P.cov2SobolevENorm s) (P.cov2SobolevENorm (s - 2)) (projectedTensorOperator rho lam ghat z)

universe u

def UniformHolderNaturalAnalyticCore : Prop :=
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
        HolderNaturalAnalyticCore C metricBounds.exponent.value H CT CV rho lam ghat z g

def UniformHolderShiftedAnalyticCore : Prop :=
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
        HolderShiftedAnalyticCore C metricBounds.exponent.value H CV rho ghat z g

def UniformSobolevAnalyticCore : Prop :=
  ∀ (coverBounds : CoverNumerics) (metricBounds : SobolevMetricNumerics)
    (s : ℝ), 4 < s →
    ∀ m : ℕ, s + 2 ≤ (m : ℝ) →
    ∀ Bcut Btransition H : ℝ≥0, 1 ≤ H →
    ∃ CS : ℝ≥0, 0 < CS ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
      ∀ C : BoundedLocalCover M, C.numerics = coverBounds →
      ∀ (P : SobolevPartition C) (L : SobolevLocalizers C),
        P.CutoffDerivativeBounds m Bcut →
        L.DerivativeBounds m Bcut →
        CoverTransitionBounds C m Btransition →
      ∀ rho : CircleAction M, SobolevActionControl P s H rho →
      ∀ (lam : ℝ) (ghat z : RawCov2 M),
        MetricSobolevAdmissible C L s metricBounds ghat →
        MetricSobolevAdmissible C L s metricBounds z →
        P.Cov2Sobolev 2 s ghat → P.Cov2Sobolev 2 s z →
        IsInvariantCov2 rho ghat → IsInvariantCov2 rho z →
        SobolevAnalyticCore P s H CS rho lam ghat z

/-- One unresolved analytic child covering all three original uniform scales.
The outer quantifier order and constants are unchanged from FullK24Statement. -/
def AnalyticCoreStatement : Prop :=
  UniformHolderNaturalAnalyticCore.{u} ∧
  UniformHolderShiftedAnalyticCore.{u} ∧
  UniformSobolevAnalyticCore.{u}

end K24.Global


