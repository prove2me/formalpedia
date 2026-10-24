-- Prove2me | Definitions.Def_K24GlobalStatement
-- name    : K24GlobalStatement
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T08:56:08.63005+00:00
-- url     : https://prove2.me/theorems/9140e2e8-3049-4225-86fe-cfe1a8c49825
-- title:
--   K24: complete conditional geometric statement and torus sharpness
-- statement:
--   The complete proposition conjoins uniform natural Hölder tensor/vector change of slice, the shifted C3-to-C1 vector clause, the real s>4 Sobolev tensor clause, and the genuine flat-torus sharpness obstruction. Numerical geometry and common-action bounds precede uniform constants; requested identities, estimates, Banach/Fréchet properties and inverse conclusions are outputs. The actual re-anchored isomorphism is the source-explicit hypothesis inside each transfer implication. Includes actual oscillating torus tensors and their norms, not scalar calibration substitutes. Every declaration is a definition or proved structural helper; no proof of the complete proposition is claimed.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — full §§1–7; inherited conventions in K16/K21/K23. Explicit norm choices and still-open organizer recorded in natural-language statement.

import Definitions.Def_K24GlobalAnalysis

/- Original source module: K24Work.Global.SobolevGeometry -/

/-!
# Concrete local Sobolev coefficient balls for K24 (3.9)

The background bounds are local real-order Sobolev bounds of actual metric
and inverse-metric coefficients. No higher Holder regularity or fixed bound
on the degree-weighted global norm of the whole metric is imposed. Smooth
collar cutoffs and coordinate transition bounds are explicit atlas data.
-/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

structure SobolevMetricNumerics where
  lower : ℝ
  lower_pos : 0 < lower
  upper : ℝ
  upper_pos : 0 < upper
  localCoefficientBound : ℝ≥0

/-- Actual collar cutoffs used to express uniform local Sobolev coefficient
bounds. Such cutoffs are ordinary bounded-cover data, not PDE estimates. -/
structure SobolevLocalizers (C : BoundedLocalCover M) where
  cutoff : C.Index → FourSpace → ℝ
  smooth : ∀ ν, ContDiff ℝ ∞ (cutoff ν)
  compactSupport : ∀ ν, HasCompactSupport (cutoff ν)
  support : ∀ ν, tsupport (cutoff ν) ⊆ (C.chart ν).outerDomain
  equals_one : ∀ ν, ∀ x ∈ closure (C.chart ν).innerDomain, cutoff ν x = 1

def SobolevLocalizers.DerivativeBounds {C : BoundedLocalCover M}
    (L : SobolevLocalizers C) (m : ℕ) (B : ℝ≥0) : Prop :=
  ∀ ν : C.Index, ∀ j ≤ m,
    derivativeENorm j Set.univ (L.cutoff ν) ≤ (B : ℝ≥0∞)

/-- Bounds on actual local transition maps between the chosen cover charts.
Only positive-order derivatives are bounded, so translating coordinate origins
does not change this condition. It contains no geometric differential operator. -/
def CoverTransitionBounds (C : BoundedLocalCover M) (m : ℕ) (B : ℝ≥0) : Prop :=
  ∀ ν mu : C.Index, ∀ U : Set FourSpace, IsOpen U →
    U ⊆ (C.chart ν).outerDomain →
    ∀ f : FourSpace → FourSpace, ContDiffOn ℝ ∞ f U →
      Set.MapsTo f U (C.chart mu).outerDomain →
      (∀ x ∈ U, (C.chart mu).lift (f x) = (C.chart ν).lift x) →
      ∀ j : ℕ, 1 ≤ j → j ≤ m → derivativeENorm j U f ≤ (B : ℝ≥0∞)

def matrixSobolevENN (s : ℝ) (f : FourSpace → Mat4) : ℝ≥0∞ :=
  (∑ i : Fin 4, ∑ j : Fin 4,
    (localSobolevENN s (fun x => f x i j)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)

def localizedMetricSobolevENN {C : BoundedLocalCover M} (L : SobolevLocalizers C)
    (s : ℝ) (g : RawCov2 M) (ν : C.Index) : ℝ≥0∞ :=
  matrixSobolevENN s (fun x => L.cutoff ν x • (C.chart ν).liftedCov2 g x)

def localizedInverseMetricSobolevENN {C : BoundedLocalCover M} (L : SobolevLocalizers C)
    (s : ℝ) (g : RawCov2 M) (ν : C.Index) : ℝ≥0∞ :=
  matrixSobolevENN s (fun x => L.cutoff ν x • (C.chart ν).inverseMetricCoefficients g x)

/-- A local Sobolev algebra ball of genuine metrics. `C²` is the canonical
representative regularity for `s>4` in dimension four, not an added norm. -/
structure MetricSobolevAdmissible (C : BoundedLocalCover M) (L : SobolevLocalizers C)
    (s : ℝ) (b : SobolevMetricNumerics) (g : RawCov2 M) : Prop where
  metric : IsMetric g
  representative : Cov2ContDiff 2 g
  ellipticityLower : ∀ ν : C.Index, ∀ x ∈ (C.chart ν).outerDomain, ∀ v : FourSpace,
    b.lower * ‖v‖ ^ 2 ≤ matrixToBilinear ((C.chart ν).liftedCov2 g x) v v
  ellipticityUpper : ∀ ν : C.Index, ∀ x ∈ (C.chart ν).outerDomain, ∀ v : FourSpace,
    matrixToBilinear ((C.chart ν).liftedCov2 g x) v v ≤ b.upper * ‖v‖ ^ 2
  coefficientBound : ∀ ν : C.Index,
    localizedMetricSobolevENN L s g ν + localizedInverseMetricSobolevENN L s g ν ≤
      (b.localCoefficientBound : ℝ≥0∞)

end K24.Global


/- Original source module: K24Work.Global.SymbolNorms -/

/-! Actual metric pointwise norms for the principal-symbol bound in K24 (3.7).
These contractions use the reference inverse metric, so the bound does not
silently depend on an uncontrolled canonical coordinate rescaling. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def metricCovectorPointNorm (g : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) : ℝ :=
  Real.sqrt (∑ a : Fin 4, ∑ b : Fin 4, inverseMetricInChart g c x a b * xi a * xi b)

def metricTensorPointNorm (g : RawCov2 M) (c : M) (x : FourSpace) (u : Mat4) : ℝ :=
  Real.sqrt (∑ a : Fin 4, ∑ b : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
    inverseMetricInChart g c x a b * inverseMetricInChart g c x i j * u a i * u b j)

end K24.Global


/- Original source module: K24Work.Global.Admissibility -/

/-!
# Concrete section domains and common-action bounds for full K24

The action bounds below are inequalities for the actual differential pullback
and the actual chosen cover norm. They explicitly retain K21/K24's common
action/norm compatibility input; this input does not follow from finite cover
degree or coordinate bounds alone. No Bianchi, tensor-defect, vector-defect,
inverse-transfer, or requested Frechet estimate is assumed here.
-/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def tensorHolderSpace (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) : Set (RawCov2 M) :=
  {u | IsSymmetricCov2 u ∧ C.Cov2Holder k alpha u}

def tensorHolderPerp (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M) : Set (RawCov2 M) :=
  {u | u ∈ tensorHolderSpace C k alpha ∧ IsNonzeroCov2 rho u}

def positiveHolderMetrics (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0) :
    Set (RawCov2 M) :=
  {q | IsMetric q ∧ C.Cov2Holder k alpha q}

def vectorHolderPerp (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M) : Set (RawVector M) :=
  {Y | C.VectorHolder k alpha Y ∧ IsNonzeroVector rho Y}

def covectorHolderPerp (C : BoundedLocalCover M) (k : ℕ) (alpha : ℝ≥0)
    (rho : CircleAction M) : Set (RawCovector M) :=
  {eta | C.CovectorHolder k alpha eta ∧ IsNonzeroCovector rho eta}

def tensorSobolevSpace {C : BoundedLocalCover M} (P : SobolevPartition C)
    (k : ℕ) (s : ℝ) : Set (RawCov2 M) :=
  {u | IsSymmetricCov2 u ∧ P.Cov2Sobolev k s u}

def tensorSobolevPerp {C : BoundedLocalCover M} (P : SobolevPartition C)
    (k : ℕ) (s : ℝ) (rho : CircleAction M) : Set (RawCov2 M) :=
  {u | u ∈ tensorSobolevSpace P k s ∧ IsNonzeroCov2 rho u}

def positiveSobolevMetrics {C : BoundedLocalCover M} (P : SobolevPartition C)
    (s : ℝ) : Set (RawCov2 M) :=
  {q | IsMetric q ∧ P.Cov2Sobolev 2 s q}

/-- Uniform boundedness of the genuine common action in all required Holder
orders. `H` is fixed before the change-of-slice constants are quantified. -/
structure HolderActionControl (C : BoundedLocalCover M) (alpha H : ℝ≥0)
    (order : ℕ) (rho : CircleAction M) : Prop where
  tensor : ∀ k ≤ order, ∀ t : Circle, ∀ u : RawCov2 M,
    C.Cov2Holder k alpha u →
    C.Cov2Holder k alpha (actionPullbackCov2 rho t u) ∧
      C.cov2ENorm k alpha (actionPullbackCov2 rho t u) ≤
        (H : ℝ≥0∞) * C.cov2ENorm k alpha u
  covector : ∀ k ≤ order, ∀ t : Circle, ∀ eta : RawCovector M,
    C.CovectorHolder k alpha eta →
    C.CovectorHolder k alpha (actionPullbackCovector rho t eta) ∧
      C.covectorENorm k alpha (actionPullbackCovector rho t eta) ≤
        (H : ℝ≥0∞) * C.covectorENorm k alpha eta
  vector : ∀ k ≤ order, ∀ t : Circle, ∀ Y : RawVector M,
    C.VectorHolder k alpha Y →
    C.VectorHolder k alpha (actionPullbackVector rho t Y) ∧
      C.vectorENorm k alpha (actionPullbackVector rho t Y) ≤
        (H : ℝ≥0∞) * C.vectorENorm k alpha Y

/-- Sobolev action compatibility in precisely the source/intermediate/target
orders. Cover degrees remain arbitrary; this is an explicit condition on the
chosen actual lifted norm rather than an inference from downstairs measure. -/
structure SobolevActionControl {C : BoundedLocalCover M} (P : SobolevPartition C)
    (s : ℝ) (H : ℝ≥0) (rho : CircleAction M) : Prop where
  tensor : ∀ j ≤ 2, ∀ t : Circle, ∀ u : RawCov2 M,
    P.Cov2Sobolev (2 - j) (s - j) u →
    P.Cov2Sobolev (2 - j) (s - j) (actionPullbackCov2 rho t u) ∧
      P.cov2SobolevENorm (s - j) (actionPullbackCov2 rho t u) ≤
        (H : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u
  covector : ∀ j ≤ 2, ∀ t : Circle, ∀ eta : RawCovector M,
    P.CovectorSobolev (2 - j) (s - j) eta →
    P.CovectorSobolev (2 - j) (s - j) (actionPullbackCovector rho t eta) ∧
      P.covectorSobolevENorm (s - j) (actionPullbackCovector rho t eta) ≤
        (H : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta

end K24.Global


/- Original source module: K24Work.Global.Conclusions -/

/-!
# Concrete conclusion bundles for the full, unproved K24 statement

Every field below is a requested CONCLUSION about the defined geometric maps
and actual section norms. None is an admissibility hypothesis. The separate
`Target.lean` will assert these bundles from the numerical geometry/common-
action hypotheses, with a clearly marked unproved theorem body.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

structure HolderProjectionConclusions (C : BoundedLocalCover M)
    (alpha H : ℝ≥0) (order : ℕ) (rho : CircleAction M) : Prop where
  tensor : ∀ k ≤ order, ∀ u : RawCov2 M, C.Cov2Holder k alpha u →
    Cov2HaarIntegrable rho u ∧
    C.Cov2Holder k alpha (cov2Pi0 rho u) ∧
    C.Cov2Holder k alpha (cov2PiPerp rho u) ∧
    IsInvariantCov2 rho (cov2Pi0 rho u) ∧
    cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
    IsNonzeroCov2 rho (cov2PiPerp rho u) ∧
    C.cov2ENorm k alpha (cov2Pi0 rho u) ≤ (H : ℝ≥0∞) * C.cov2ENorm k alpha u ∧
    C.cov2ENorm k alpha (cov2PiPerp rho u) ≤
      ((1 + H : ℝ≥0) : ℝ≥0∞) * C.cov2ENorm k alpha u
  covector : ∀ k ≤ order, ∀ eta : RawCovector M, C.CovectorHolder k alpha eta →
    CovectorHaarIntegrable rho eta ∧
    C.CovectorHolder k alpha (covectorPi0 rho eta) ∧
    C.CovectorHolder k alpha (covectorPiPerp rho eta) ∧
    IsInvariantCovector rho (covectorPi0 rho eta) ∧
    covectorPi0 rho (covectorPi0 rho eta) = covectorPi0 rho eta ∧
    IsNonzeroCovector rho (covectorPiPerp rho eta) ∧
    C.covectorENorm k alpha (covectorPi0 rho eta) ≤
      (H : ℝ≥0∞) * C.covectorENorm k alpha eta ∧
    C.covectorENorm k alpha (covectorPiPerp rho eta) ≤
      ((1 + H : ℝ≥0) : ℝ≥0∞) * C.covectorENorm k alpha eta
  vector : ∀ k ≤ order, ∀ Y : RawVector M, C.VectorHolder k alpha Y →
    VectorHaarIntegrable rho Y ∧
    C.VectorHolder k alpha (vectorPi0 rho Y) ∧
    C.VectorHolder k alpha (vectorPiPerp rho Y) ∧
    IsInvariantVector rho (vectorPi0 rho Y) ∧
    vectorPi0 rho (vectorPi0 rho Y) = vectorPi0 rho Y ∧
    IsNonzeroVector rho (vectorPiPerp rho Y) ∧
    C.vectorENorm k alpha (vectorPi0 rho Y) ≤ (H : ℝ≥0∞) * C.vectorENorm k alpha Y ∧
    C.vectorENorm k alpha (vectorPiPerp rho Y) ≤
      ((1 + H : ℝ≥0) : ℝ≥0∞) * C.vectorENorm k alpha Y

/-- Exact source identities, expressed using the literal nonlinear map,
its actual coefficient variation, and genuine global geometric operators. -/
structure ExactChangeOfSliceConclusions (C : BoundedLocalCover M) (alpha : ℝ≥0)
    (rho : CircleAction M) (lam : ℝ) (ghat z g : RawCov2 M) : Prop where
  cancellation : covectorPiPerp rho (bianchi ghat (z - ghat)) = 0
  equivariant_fixed : ∀ t : Circle, ∀ q ∈ positiveHolderMetrics C 2 alpha,
    partialGauge rho lam ghat (actionPullbackCov2 rho t q) =
      actionPullbackCov2 rho t (partialGauge rho lam ghat q)
  equivariant_reanchored : ∀ t : Circle, ∀ q ∈ positiveHolderMetrics C 2 alpha,
    partialGauge rho lam z (actionPullbackCov2 rho t q) =
      actionPullbackCov2 rho t (partialGauge rho lam z q)
  product_rule : ∀ u ∈ tensorHolderSpace C 2 alpha,
    partialGaugeVariation rho lam ghat z u = partialGaugeProductRule rho lam ghat z u
  dangerous_term_zero : ∀ u ∈ tensorHolderSpace C 2 alpha,
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) = 0
  bianchi_sector : ∀ u ∈ tensorHolderPerp C 2 alpha rho,
    IsNonzeroCovector rho (bianchi ghat u) ∧ IsNonzeroCovector rho (bianchi z u)
  fixed_linearization : ∀ u ∈ tensorHolderPerp C 2 alpha rho,
    partialGaugeVariation rho lam ghat z u =
      einsteinLinearization lam z u + deltaStar z (bianchi ghat u)
  reanchored_linearization : ∀ u ∈ tensorHolderPerp C 2 alpha rho,
    partialGaugeVariation rho lam z z u =
      einsteinLinearization lam z u + deltaStar z (bianchi z u)
  tensor_sector : ∀ u ∈ tensorHolderPerp C 2 alpha rho,
    projectedTensorOperator rho lam ghat z u = partialGaugeVariation rho lam ghat z u ∧
    projectedTensorOperator rho lam z z u = partialGaugeVariation rho lam z z u
  tensor_difference : ∀ u ∈ tensorHolderPerp C 2 alpha rho,
    projectedTensorOperator rho lam ghat z u - projectedTensorOperator rho lam z z u =
      tensorDefect ghat z u
  connection_formula : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
    ∀ k i j : Fin 4, connectionDifferenceInChart ghat z c x k i j =
      connectionDifferenceExpansion ghat z c x k i j
  bianchi_formula : ∀ u ∈ tensorHolderSpace C 2 alpha, ∀ (c : M) (x : FourSpace),
    x ∈ (chartAt FourSpace c).target → ∀ j : Fin 4,
      bianchiInChart ghat u c x j - bianchiInChart z u c x j =
        bianchiDifferenceExpansion ghat z u c x j
  principal_symbol : ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
    ∀ (xi : Fin 4 → ℝ) (a : Mat4) (i j : Fin 4),
      tensorDefectPrincipalSymbol ghat z c x xi a i j =
        tensorDefectSymbolFormula ghat z c x xi a i j
  center_vector_difference : ∀ Y : RawVector M, C.VectorHolder 2 alpha Y →
    projectedVectorOperator rho ghat z Y - projectedVectorOperator rho z z Y =
      covectorPiPerp rho (bianchi ghat (killing z Y) - bianchi z (killing z Y))
  actual_vector_difference : ∀ Y : RawVector M, C.VectorHolder 2 alpha Y →
    projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y =
      projectedActualVectorDefect rho ghat z g Y
  weitzenbock : ∀ Y : RawVector M, C.VectorHolder 2 alpha Y →
    bianchi z (killing z Y) = roughVectorLaplacianFlat z Y - ricciVectorFlat z Y

/-- K24's natural Holder tensor and vector conclusions, with actual Frechet
differentiability, spaces, estimates, and conditional geometric inverse transfer. -/
structure HolderNaturalConclusions (C : BoundedLocalCover M) (alpha H CT CV : ℝ≥0)
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
  tensor_inverse_transfer : ∀ CA : ℝ≥0, 0 < CA →
    SectionIsomorphism (tensorHolderPerp C 2 alpha rho) (tensorHolderPerp C 0 alpha rho)
      (C.cov2ENorm 2 alpha) (C.cov2ENorm 0 alpha) (projectedTensorOperator rho lam z z) →
    SectionInverseBound (tensorHolderPerp C 2 alpha rho) (C.cov2ENorm 2 alpha)
      (C.cov2ENorm 0 alpha) (projectedTensorOperator rho lam z z) CA →
    (CA : ℝ≥0∞) * sectionOperatorENorm (tensorHolderPerp C 2 alpha rho)
      (C.cov2ENorm 2 alpha) (C.cov2ENorm 0 alpha)
      (fun u => projectedTensorOperator rho lam ghat z u - projectedTensorOperator rho lam z z u)
      < (1 / 2 : ℝ≥0∞) →
    SectionIsomorphism (tensorHolderPerp C 2 alpha rho) (tensorHolderPerp C 0 alpha rho)
      (C.cov2ENorm 2 alpha) (C.cov2ENorm 0 alpha) (projectedTensorOperator rho lam ghat z) ∧
    SectionInverseBound (tensorHolderPerp C 2 alpha rho) (C.cov2ENorm 2 alpha)
      (C.cov2ENorm 0 alpha) (projectedTensorOperator rho lam ghat z) (2 * CA) ∧
    SectionDualGap (tensorHolderPerp C 2 alpha rho) (tensorHolderPerp C 0 alpha rho)
      (C.cov2ENorm 2 alpha) (C.cov2ENorm 0 alpha) (projectedTensorOperator rho lam ghat z) (2 * CA)
  vector_inverse_transfer : ∀ CB : ℝ≥0, 0 < CB →
    SectionIsomorphism (vectorHolderPerp C 2 alpha rho) (covectorHolderPerp C 0 alpha rho)
      (C.vectorENorm 2 alpha) (C.covectorENorm 0 alpha) (projectedVectorOperator rho z z) →
    SectionInverseBound (vectorHolderPerp C 2 alpha rho) (C.vectorENorm 2 alpha)
      (C.covectorENorm 0 alpha) (projectedVectorOperator rho z z) CB →
    (CB : ℝ≥0∞) * sectionOperatorENorm (vectorHolderPerp C 2 alpha rho)
      (C.vectorENorm 2 alpha) (C.covectorENorm 0 alpha)
      (fun Y => projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y)
      < (1 / 2 : ℝ≥0∞) →
    SectionIsomorphism (vectorHolderPerp C 2 alpha rho) (covectorHolderPerp C 0 alpha rho)
      (C.vectorENorm 2 alpha) (C.covectorENorm 0 alpha) (projectedVectorOperator rho ghat g) ∧
    SectionInverseBound (vectorHolderPerp C 2 alpha rho) (C.vectorENorm 2 alpha)
      (C.covectorENorm 0 alpha) (projectedVectorOperator rho ghat g) (2 * CB) ∧
    SectionDualGap (vectorHolderPerp C 2 alpha rho) (covectorHolderPerp C 0 alpha rho)
      (C.vectorENorm 2 alpha) (C.covectorENorm 0 alpha) (projectedVectorOperator rho ghat g) (2 * CB)
  center_comparison : ∀ q ∈ tensorHolderSpace C 2 alpha,
    C.cov2ENorm 2 alpha (cov2Pi0 rho (q - ghat)) ≤
      (H : ℝ≥0∞) * C.cov2ENorm 2 alpha (q - ghat)

/-- The shifted vector pair retains third-order differences for BOTH metrics. -/
structure HolderShiftedConclusions (C : BoundedLocalCover M) (alpha H CV : ℝ≥0)
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
  inverse_transfer : ∀ CB : ℝ≥0, 0 < CB →
    SectionIsomorphism (vectorHolderPerp C 3 alpha rho) (covectorHolderPerp C 1 alpha rho)
      (C.vectorENorm 3 alpha) (C.covectorENorm 1 alpha) (projectedVectorOperator rho z z) →
    SectionInverseBound (vectorHolderPerp C 3 alpha rho) (C.vectorENorm 3 alpha)
      (C.covectorENorm 1 alpha) (projectedVectorOperator rho z z) CB →
    (CB : ℝ≥0∞) * sectionOperatorENorm (vectorHolderPerp C 3 alpha rho)
      (C.vectorENorm 3 alpha) (C.covectorENorm 1 alpha)
      (fun Y => projectedVectorOperator rho ghat g Y - projectedVectorOperator rho z z Y)
      < (1 / 2 : ℝ≥0∞) →
    SectionIsomorphism (vectorHolderPerp C 3 alpha rho) (covectorHolderPerp C 1 alpha rho)
      (C.vectorENorm 3 alpha) (C.covectorENorm 1 alpha) (projectedVectorOperator rho ghat g) ∧
    SectionInverseBound (vectorHolderPerp C 3 alpha rho) (C.vectorENorm 3 alpha)
      (C.covectorENorm 1 alpha) (projectedVectorOperator rho ghat g) (2 * CB) ∧
    SectionDualGap (vectorHolderPerp C 3 alpha rho) (covectorHolderPerp C 1 alpha rho)
      (C.vectorENorm 3 alpha) (C.covectorENorm 1 alpha) (projectedVectorOperator rho ghat g) (2 * CB)

/-- Real-order Sobolev version, on canonical classical representatives in the
source/target orders where the Sobolev embedding supplies such representatives.
There is no integer-only substitution and no added Holder norm. -/
structure SobolevConclusions {C : BoundedLocalCover M} (P : SobolevPartition C)
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
  inverse_transfer : ∀ CA : ℝ≥0, 0 < CA →
    SectionIsomorphism (tensorSobolevPerp P 2 s rho) (tensorSobolevPerp P 0 (s - 2) rho)
      (P.cov2SobolevENorm s) (P.cov2SobolevENorm (s - 2)) (projectedTensorOperator rho lam z z) →
    SectionInverseBound (tensorSobolevPerp P 2 s rho) (P.cov2SobolevENorm s)
      (P.cov2SobolevENorm (s - 2)) (projectedTensorOperator rho lam z z) CA →
    (CA : ℝ≥0∞) * sectionOperatorENorm (tensorSobolevPerp P 2 s rho)
      (P.cov2SobolevENorm s) (P.cov2SobolevENorm (s - 2))
      (fun u => projectedTensorOperator rho lam ghat z u - projectedTensorOperator rho lam z z u)
      < (1 / 2 : ℝ≥0∞) →
    SectionIsomorphism (tensorSobolevPerp P 2 s rho) (tensorSobolevPerp P 0 (s - 2) rho)
      (P.cov2SobolevENorm s) (P.cov2SobolevENorm (s - 2)) (projectedTensorOperator rho lam ghat z) ∧
    SectionInverseBound (tensorSobolevPerp P 2 s rho) (P.cov2SobolevENorm s)
      (P.cov2SobolevENorm (s - 2)) (projectedTensorOperator rho lam ghat z) (2 * CA) ∧
    SectionDualGap (tensorSobolevPerp P 2 s rho) (tensorSobolevPerp P 0 (s - 2) rho)
      (P.cov2SobolevENorm s) (P.cov2SobolevENorm (s - 2))
      (projectedTensorOperator rho lam ghat z) (2 * CA)

end K24.Global


/- Original source module: K24Work.Global.FlatTorus -/

/-!
# Actual flat-torus data for the K24 regularity obstruction

The base is the compact four-torus `Fin 4 → Circle`, not Euclidean space.
Its `FourSpace` charted structure is pushed forward by the actual periodic
map `x ↦ (exp (x_i))_i`. Frames and tensors use the manifold differential of
that map. Smoothness of this atlas and the flat-frame identities are explicit
theorem obligations in `FlatTorusTargets.lean`. No estimate or admitted proof
occurs in this definition file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

noncomputable section
open Filter Topology
open scoped Manifold ContDiff BigOperators NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus

abbrev Torus := Fin 4 → Circle

def quotientMap (x : FourSpace) : Torus := fun i => Circle.exp (x i)

def representative (p : Torus) : FourSpace :=
  WithLp.toLp 2 (fun i => Complex.arg (p i))

theorem quotientMap_representative (p : Torus) : quotientMap (representative p) = p := by
  funext i
  exact Circle.exp_arg (p i)

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  fun p => ⟨representative p, quotientMap_representative p⟩

theorem piExp_isLocalHomeomorph :
    IsLocalHomeomorph (fun x : Fin 4 → ℝ => fun i => Circle.exp (x i)) := by
  intro x
  choose e he heq using fun i => isLocalHomeomorph_circleExp (x i)
  refine ⟨OpenPartialHomeomorph.pi e, ?_, ?_⟩
  · exact fun i _ => he i
  · funext y i
    exact congrFun (heq i) (y i)

theorem quotientMap_isLocalHomeomorph : IsLocalHomeomorph quotientMap := by
  exact piExp_isLocalHomeomorph.comp
    (PiLp.homeomorph 2 (fun _ : Fin 4 => ℝ)).isLocalHomeomorph

/-- A genuine charted structure on the compact quotient, with Euclidean
four-space as its chart model. Smooth compatibility is separately targeted. -/
instance torusChartedSpace : ChartedSpace FourSpace Torus :=
  quotientMap_isLocalHomeomorph.chartedSpaceOfRightInverse quotientMap_representative

/-- Differential of the actual universal-cover map at a specified lift. -/
def coverDifferential (x : FourSpace) : FourSpace →L[ℝ] TangentSpace I4 (quotientMap x) :=
  mfderiv I4 I4 quotientMap x

def frame (p : Torus) (i : Fin 4) : TangentSpace I4 p :=
  coverDifferential (representative p) (basisVector i)

def coframe (p : Torus) (i : Fin 4) : TangentSpace I4 p →L[ℝ] ℝ :=
  (coordProj i).comp (coverDifferential (representative p)).inverse

def flatMetric : RawCov2 Torus :=
  fun p => ∑ i : Fin 4, (coframe p i).smulRight (coframe p i)

def amplitude (alpha : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (-(3 + alpha))

/-- The globally defined scalar `n^{-(3+α)} sin(n x₁)` on the actual torus. -/
def oscillatingScalar (alpha : ℝ) (n : ℕ) (p : Torus) : ℝ :=
  amplitude alpha n * ((p 0 ^ n : Circle) : ℂ).im

def perturbation (alpha : ℝ) (n : ℕ) : RawCov2 Torus :=
  fun p => oscillatingScalar alpha n p • (coframe p 0).smulRight (coframe p 0)

def nearbyMetric (alpha : ℝ) (n : ℕ) : RawCov2 Torus :=
  flatMetric + perturbation alpha n

def testVector : RawVector Torus :=
  fun p => ((p 1 : Circle) : ℂ).re • frame p 0

/-- The marked circle rotates the second factor, i.e. translates `x₂`. -/
def translate (t : Circle) (p : Torus) : Torus :=
  fun i => if i = 1 then t * p i else p i

theorem translate_one (p : Torus) : translate 1 p = p := by
  funext i
  simp [translate]

theorem translate_mul (s t : Circle) (p : Torus) :
    translate (s * t) p = translate s (translate t p) := by
  funext i
  by_cases hi : i = 1 <;> simp [translate, hi, mul_assoc]

/-- Literal coefficients of the pullback of an actual torus tensor. -/
def coverCov2 (u : RawCov2 Torus) (x : FourSpace) : Mat4 :=
  fun i j => pullbackCov2 quotientMap u x (basisVector i) (basisVector j)

def coverCovector (u : RawCovector Torus) (x : FourSpace) : Fin 4 → ℝ :=
  fun i => pullbackCovector quotientMap u x (basisVector i)

def coverVector (Y : RawVector Torus) (x : FourSpace) : FourSpace :=
  (coverDifferential x).inverse (Y (quotientMap x))

/-- Global periodic-cover norms of actual torus sections. The supremum is over
the full cover; periodicity makes it a genuine flat-torus Hölder norm.
Finiteness of the particular smooth sections is a theorem conclusion. -/
def tensorHolderENorm (k : ℕ) (alpha : ℝ≥0) (u : RawCov2 Torus) : ℝ≥0∞ :=
  coordinateHolderENorm k alpha Set.univ (coverCov2 u)

def covectorHolderENorm (k : ℕ) (alpha : ℝ≥0) (u : RawCovector Torus) : ℝ≥0∞ :=
  coordinateHolderENorm k alpha Set.univ (coverCovector u)

def vectorHolderENorm (k : ℕ) (alpha : ℝ≥0) (Y : RawVector Torus) : ℝ≥0∞ :=
  coordinateHolderENorm k alpha Set.univ (coverVector Y)

def tensorHolderNorm (k : ℕ) (alpha : ℝ≥0) (u : RawCov2 Torus) : ℝ :=
  (tensorHolderENorm k alpha u).toReal

def covectorHolderNorm (k : ℕ) (alpha : ℝ≥0) (u : RawCovector Torus) : ℝ :=
  (covectorHolderENorm k alpha u).toReal

def vectorHolderNorm (k : ℕ) (alpha : ℝ≥0) (Y : RawVector Torus) : ℝ :=
  (vectorHolderENorm k alpha Y).toReal

def unprojectedDefect (alpha : ℝ) (n : ℕ) : RawCovector Torus :=
  bianchi flatMetric (lieTensor testVector (perturbation alpha n))

def projectedDefect (rho : CircleAction Torus) (alpha : ℝ) (n : ℕ) : RawCovector Torus :=
  covectorPiPerp rho (unprojectedDefect alpha n)

/-- The difference of the actual vector operators, tested on the fixed V. -/
def actualVectorDifference (rho : CircleAction Torus) (alpha : ℝ) (n : ℕ) : RawCovector Torus :=
  covectorPiPerp rho
    (vectorOperator flatMetric (nearbyMetric alpha n) testVector -
      vectorOperator flatMetric flatMetric testVector)

def liftedOscillation (alpha : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  amplitude alpha n * Real.sin ((n : ℝ) * r)

/-- The explicit result expected from the genuine geometric differential
expression. Its equality to that expression is a separate target. -/
def expectedDefectCoefficients (alpha : ℝ) (n : ℕ) (x : FourSpace) : Fin 4 → ℝ :=
  fun j => if j = 0 then
      Real.cos (x 1) *
        (liftedOscillation alpha n (x 0) -
          (1 / 2 : ℝ) * deriv (deriv (liftedOscillation alpha n)) (x 0))
    else if j = 1 then
      (1 / 2 : ℝ) * Real.sin (x 1) * deriv (liftedOscillation alpha n) (x 0)
    else 0

/-- Complete original K24 section 5.1 sharpness conclusion on the actual torus.
This proposition includes geometric positivity, Haar integrability, norm
finiteness, convergence, the lower bound and failure of the shifted estimate. -/
def SharpnessStatement : Prop :=
  ∀ alpha : HolderExponent,
    IsManifold I4 ∞ Torus ∧
    ∃ rho : CircleAction Torus, ∃ C : ℝ,
      rho.act = translate ∧ 0 < C ∧
      IsMetric flatMetric ∧ IsInvariantCov2 rho flatMetric ∧
      VectorHaarIntegrable rho testVector ∧ IsNonzeroVector rho testVector ∧
      vectorHolderENorm 3 alpha.value testVector < ⊤ ∧
      0 < vectorHolderNorm 3 alpha.value testVector ∧
      (∀ n : ℕ,
        tensorHolderENorm 2 alpha.value (perturbation alpha.value n) < ⊤ ∧
        tensorHolderENorm 3 alpha.value (perturbation alpha.value n) < ⊤ ∧
        covectorHolderENorm 1 alpha.value (projectedDefect rho alpha.value n) < ⊤ ∧
        CovectorHaarIntegrable rho (unprojectedDefect alpha.value n) ∧
        tensorHolderNorm 3 alpha.value (perturbation alpha.value n) ≤ C) ∧
      Tendsto (fun n : ℕ => tensorHolderNorm 2 alpha.value (perturbation alpha.value n))
        atTop (𝓝 0) ∧
      (∀ n : ℕ, 2 ≤ n →
        IsMetric (nearbyMetric alpha.value n) ∧
        Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
          covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n) ∧
        actualVectorDifference rho alpha.value n = projectedDefect rho alpha.value n) ∧
      ¬ (∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n →
        covectorHolderNorm 1 alpha.value (actualVectorDifference rho alpha.value n) ≤
          K * tensorHolderNorm 2 alpha.value (perturbation alpha.value n) *
            vectorHolderNorm 3 alpha.value testVector)

end K24.Global.FlatTorus


/- Original source module: K24Work.Global.Statement -/

/-!
# The full K24 proposition, with genuine definitions and explicit quantifiers

Pinned original: liushuijixiang/siwei-einstein at
8c02be189f097080feca952347c9104bfb986242,
K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md.

This file defines the mathematical proposition; it proves none of its
analytic conclusions. Each numerical geometry/action bound is fixed BEFORE
the uniform conclusion constant, which is then uniform over manifolds,
covers, actions, references, centers, actual metrics, and sections.

The natural Holder, shifted vector, and real-order Sobolev statements are
separate conjuncts. Thus the natural statement is not strengthened to demand
third-order metric regularity, and Sobolev metrics are not strengthened to
high-order Holder metrics. The same-window geometry and the initial adapted
isomorphisms remain conditional input. No Einstein condition is imposed on
the comparison metrics, and no open organizer is asserted to exist.
-/

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal Manifold ContDiff

namespace K24.Global

universe u

def UniformHolderNaturalStatement : Prop :=
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
        HolderNaturalConclusions C metricBounds.exponent.value H CT CV rho lam ghat z g

def UniformHolderShiftedStatement : Prop :=
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
        HolderShiftedConclusions C metricBounds.exponent.value H CV rho ghat z g

/-- The Sobolev background balls use local `H^s` coefficient bounds and
ordinary bounded atlas/cutoff data. Whole metric `H^s_cov` norms need only be
finite; no fixed degree-dependent global bound is assumed. -/
def UniformSobolevStatement : Prop :=
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
        SobolevConclusions P s H CS rho lam ghat z

/-- The complete conditional geometric K24 problem, including the real torus
regularity obstruction. This is not the abstract Neumann lemma and not a
claim that any of its unresolved proofs or organizer inputs are available. -/
def FullK24Statement : Prop :=
  UniformHolderNaturalStatement.{u} ∧
  UniformHolderShiftedStatement.{u} ∧
  UniformSobolevStatement.{u} ∧
  FlatTorus.SharpnessStatement

end K24.Global


