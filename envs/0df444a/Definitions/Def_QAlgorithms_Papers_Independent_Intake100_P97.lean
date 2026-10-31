-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97
-- name    : QAlgorithms_Papers_Independent_Intake100_P97
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T16:00:22.236833+00:00
-- url     : https://prove2.me/theorems/af160d1c-48ea-40f4-b6ef-aefafc2a34dc
-- title:
--   Definitions for Entropic fluctuations in Gaussian dynamical systems
-- statement:
--   The objects the formalized statements of *Entropic fluctuations in Gaussian dynamical systems* (arXiv:1509.03244) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CylinderPhase`
--   - `RealCoordinateHilbert`
--   - `RealCoordinateOperator`
--   - `IsWeight`: Positive normalized weights, §2.1, PDF p.3.
--   - `weightedDistance`: The displayed metric in §2.1, PDF p.3; the ambient topology is the product topology.
--   - `weightedEnergy`: Extended weighted squared norm; an infinite energy is never replaced by zero.
--   - `inWeighted`: The weighted support space X_l, §2.1, PDF p.4.
--   - `inDual`: X_l^* as a subspace of K, §2.1, PDF p.4.
--   - `hilbertCoordinate`: Standard coordinate basis used for all operator entries.
--   - `entry`: Matrix elements are taken in the real standard coordinate basis.
--   - `IsCovariance`: Bounded self-adjoint covariance with a uniform positive lower bound, PDF p.4.
--   - `cylinderMatrix`: Finite compression of a covariance, including the zero-dimensional case.
--   - `cylinderDensity`: The finite-dimensional Lebesgue density displayed in §2.1, PDF p.4.
--   - `IsCylinderGaussian`: A genuine probability measure whose every finite coordinate marginal has the source density.
--   - `cylinderGaussian`: The unique cylinder law, selected by its defining marginals. The fallback is irrelevant under IsCovariance; existence and uniqueness are conclusions below.
--   - `weightedVector`: Weighted coordinates identify X_l isometrically with ordinary real ℓ².
--   - `weightedPhase`: Inverse of the weighted coordinate identification on positive weights.
--   - `ExtendsWeighted`: Agreement on the dense unweighted Hilbert subspace pins the extension uniquely.
--   - `WeightedCompatible`: A continuous extension exists; this property is not assumed for L in the flow theorem.
--   - `weightedExtension`: The extension determined by A, rather than a freely supplied flow.
--   - `flow`: The exact piecewise flow in (6), PDF p.4, including the off-X_l identity branch.
--   - `covarianceAt`: Evolved covariance in the pushforward direction, PDF p.5.
--   - `operatorInverse`: Inverse in the bounded-operator algebra. Coercive covariances always take the first branch.
--   - `realTraceSize`: Extended real trace norm, §2.1, PDF p.4. The finite branch reuses the accepted real-Hilbert modulus trace norm; non-trace-class operators have value ∞. This extension is needed for cutoff errors and trace-norm difference quotients.
--   - `fredholmPlus`: Fredholm determinant det(I+A), given by its absolutely convergent principal-minor series on the trace-class ideal. The empty principal minor contributes 1.
--   - `cutoffOperator`: Finite coordinate projection in an arbitrary enumeration of the countable set.
--   - `finiteQuadratic`: The corresponding genuine finite-coordinate quadratic polynomial.
--   - `quadraticCutoff`: A summably fast trace-norm approximation. For trace-class A this defining set is nonempty. Fast cutoffs make the pointwise representative valid for every bounded Gaussian covariance, including mutually singular limiting laws.
--   - `gaussianQuadratic`: Canonical Gaussian quadratic observable: the almost sure, summably fast finite-coordinate limit. It equals (x,Ax) on K. The zero fallback is used only when the real sequence has no limit.
--   - `HasBilateralTraceDerivative`: Trace-norm differentiability, expressed without transporting an unaudited Banach instance.
--   - `precisionShift`: The precision increment T_t=D_t⁻¹-D⁻¹.
--   - `G1`: Exactly (G1), differentiability at zero in the real trace norm, PDF p.5.
--   - `productionOperator`: The actual entropy-production operator, not a free derivative parameter, (8), PDF p.5.
--   - `production`: Entropy-production observable, with its actual Gaussian quadratic representative.
--   - `asL1`: Conversion to L¹, with no integrability hidden in its type. Integrability is stated as a conclusion whenever this conversion is used.
--   - `realRNDensity`: The actual real Radon–Nikodym density, used only for the finite probability laws.
--   - `nonpositiveRelativeEntropy`: For probabilities, a nonintegrable log density has entropy -∞. The AC guard also gives -∞ for singular laws. Every density formula below separately states AC.
--   - `G2`: Uniform coercive bounds for every real time, (G2), PDF p.6.
--   - `G3`: (G3) requires actual strong limits in both time directions, PDF p.6.
--   - `futureCovariance`: The constructed future covariance; uniqueness follows from strong convergence.
--   - `pastCovariance`: The constructed past covariance.
--   - `G4`: (G4), including a continuous action on the weighted Hilbert space.
--   - `weightedTimeReversal`: Coordinate action of time reversal, identity outside X_l.
--   - `extendedProbabilityLog`: Logarithm retaining both infinite endpoints, §2.1, PDF pp.3–4.
--   - `gaussianCumulant`: The actual finite-time reference-state Rényi functional (12), with divergent moments assigned +∞ before any conversion to a real number.
--   - `realCumulant`: Real branch, used only locally inside the finite moment domain.
--   - `gaussianMomentDomain`: Exact finite-time positivity domain J_t, PDF p.7.
--   - `minimalDomain`: The open minimal interval, as used in the proof, rather than an assertion that endpoints cannot belong to the raw set-liminf, PDF p.7.
--   - `ExtendedConvexOn`: Jensen convexity for extended-real functions, with nonnegative real weights.
--   - `gaussianCutPlane`: The two open half-planes together with the real interval S.
--   - `canonicalLogDensity`: The canonical logarithmic density (37), valid under all bounded Gaussian laws, not an arbitrary version of the reference-measure RN derivative.
--   - `nessCumulant`: Actual NESS moment, §2.5, PDF p.9.
--   - `nessDomain`: Exact NESS positivity domain (26).
--   - `minimalNessDomain`: Interior of the eventual NESS domains, exactly as in Theorem 2.6(3).
--   - `realLimit`: A real limiting value; each result using this definition states actual convergence, so the fallback does not assert existence of a limit.
--   - `limitingCumulant`: Asymptotic reference cumulant on its open finite domain.
--   - `limitingNessCumulant`: Asymptotic NESS cumulant on its open finite domain.
--   - `rateFunction`: Legendre–Fenchel transform with the source's sign and extended-real supremum.
--   - `productionAverage`: The time average of the actual evolved entropy-production observable.
--   - `logEventRate`: Scaled log probability; zero probabilities give -∞, not Real.log 0.
--   - `SignedBorelPair`: Jordan data for a possibly infinite-total-variation signed Borel measure. Local finiteness and the weighted variation condition are imposed by LogPotential; this is deliberately not Mathlib's finite SignedMeasure type.
--   - `LogPotential`: Logarithmic potential (16), including integrability before real subtraction. The support condition uses zero mass on the open interval, equivalently support in its closed complement.
--   - `perturbedCovariance`: Precision perturbation D^P=(D⁻¹+P)⁻¹, §2.6, PDF p.11.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, https://arxiv.org/abs/1509.03244v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

/-!
Statements from Jakšić, Pillet and Shirikyan, arXiv:1509.03244v1.
Paper-specific constructions live in this namespace. The real-Hilbert trace-class
predicate, trace norm, trace and positive square root are imported from the pinned
accepted Next46.P02 module. The phase space is the countable product of real lines,
not the unweighted Hilbert space. Trace size extends the imported norm by ∞
outside the real trace-class ideal.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

abbrev CylinderPhase (G : Type*) := G → ℝ

abbrev RealCoordinateHilbert (G : Type*) := lp (fun _ : G => ℝ) 2

abbrev RealCoordinateOperator (G : Type*) := RealCoordinateHilbert G →L[ℝ] RealCoordinateHilbert G

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Positive normalized weights, §2.1, PDF p.3. -/
def IsWeight (l : G → ℝ) : Prop :=
  (∀ i, 0 < l i) ∧ Summable l ∧ ∑' i, l i = 1

/-- The displayed metric in §2.1, PDF p.3; the ambient topology is the product topology. -/
def weightedDistance (l : G → ℝ) (x y : CylinderPhase G) : ℝ :=
  ∑' i, l i * |x i - y i| / (1 + |x i - y i|)

/-- Extended weighted squared norm; an infinite energy is never replaced by zero. -/
def weightedEnergy (l : G → ℝ) (x : CylinderPhase G) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (l i * (x i) ^ 2)

/-- The weighted support space X_l, §2.1, PDF p.4. -/
def inWeighted (l : G → ℝ) (x : CylinderPhase G) : Prop :=
  weightedEnergy l x < ⊤

/-- X_l^* as a subspace of K, §2.1, PDF p.4. -/
def inDual (l : G → ℝ) (y : RealCoordinateHilbert G) : Prop :=
  Summable (fun i => (l i)⁻¹ * (y i) ^ 2)

/-- Standard coordinate basis used for all operator entries. -/
def hilbertCoordinate (i : G) : RealCoordinateHilbert G := lp.single 2 i 1

/-- Matrix elements are taken in the real standard coordinate basis. -/
def entry (A : RealCoordinateOperator G) (i j : G) : ℝ :=
  inner ℝ (hilbertCoordinate i) (A (hilbertCoordinate j))

/-- Bounded self-adjoint covariance with a uniform positive lower bound, PDF p.4. -/
def IsCovariance (D : RealCoordinateOperator G) : Prop :=
  ContinuousLinearMap.adjoint D = D ∧
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ v (D v)

/-- Finite compression of a covariance, including the zero-dimensional case. -/
def cylinderMatrix (D : RealCoordinateOperator G) (I : Finset G) : Matrix I I ℝ :=
  fun i j => entry D i j

/-- The finite-dimensional Lebesgue density displayed in §2.1, PDF p.4. -/
def cylinderDensity (D : RealCoordinateOperator G) (I : Finset G)
    (x : EuclideanSpace ℝ I) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ I.card * (cylinderMatrix D I).det))⁻¹ *
    Real.exp (- (∑ i, ∑ j, x i * ((cylinderMatrix D I)⁻¹ i j) * x j) / 2)

/-- A genuine probability measure whose every finite coordinate marginal has the source density. -/
def IsCylinderGaussian (mu : Measure (CylinderPhase G)) (D : RealCoordinateOperator G) : Prop :=
  IsProbabilityMeasure mu ∧ ∀ I : Finset G,
    mu.map (fun x => WithLp.toLp 2 (fun i : I => x i)) =
      (volume : Measure (EuclideanSpace ℝ I)).withDensity
        (fun x => ENNReal.ofReal (cylinderDensity D I x))

/-- The unique cylinder law, selected by its defining marginals. The fallback is
irrelevant under IsCovariance; existence and uniqueness are conclusions below. -/
def cylinderGaussian (D : RealCoordinateOperator G) : Measure (CylinderPhase G) :=
  if h : ∃ mu, IsCylinderGaussian mu D then Classical.choose h else Measure.dirac 0

/-- Weighted coordinates identify X_l isometrically with ordinary real ℓ². -/
def weightedVector (l : G → ℝ) (x : CylinderPhase G) : RealCoordinateHilbert G :=
  if h : Memℓp (fun i => Real.sqrt (l i) * x i) 2 then
    ⟨fun i => Real.sqrt (l i) * x i, h⟩ else 0

/-- Inverse of the weighted coordinate identification on positive weights. -/
def weightedPhase (l : G → ℝ) (z : RealCoordinateHilbert G) : CylinderPhase G :=
  fun i => z i / Real.sqrt (l i)

/-- Agreement on the dense unweighted Hilbert subspace pins the extension uniquely. -/
def ExtendsWeighted (l : G → ℝ) (A E : RealCoordinateOperator G) : Prop :=
  ∀ v : RealCoordinateHilbert G, E (weightedVector l (fun i => v i)) =
    weightedVector l (fun i => A v i)

/-- A continuous extension exists; this property is not assumed for L in the flow theorem. -/
def WeightedCompatible (l : G → ℝ) (A : RealCoordinateOperator G) : Prop :=
  ∃ E : RealCoordinateOperator G, ExtendsWeighted l A E

/-- The extension determined by A, rather than a freely supplied flow. -/
def weightedExtension (l : G → ℝ) (A : RealCoordinateOperator G) : RealCoordinateOperator G :=
  if h : WeightedCompatible l A then Classical.choose h else 0

/-- The exact piecewise flow in (6), PDF p.4, including the off-X_l identity branch. -/
def flow (l : G → ℝ) (L : RealCoordinateOperator G) (t : ℝ) (x : CylinderPhase G) : CylinderPhase G :=
  if inWeighted l x then
    weightedPhase l ((NormedSpace.exp (t • weightedExtension l L)) (weightedVector l x))
  else x

/-- Evolved covariance in the pushforward direction, PDF p.5. -/
def covarianceAt (D L : RealCoordinateOperator G) (t : ℝ) : RealCoordinateOperator G :=
  NormedSpace.exp (t • L) * D * NormedSpace.exp (t • ContinuousLinearMap.adjoint L)

/-- Inverse in the bounded-operator algebra. Coercive covariances always take the first branch. -/
def operatorInverse (A : RealCoordinateOperator G) : RealCoordinateOperator G :=
  if h : ∃ B : RealCoordinateOperator G, A * B = 1 ∧ B * A = 1 then Classical.choose h else 0

/-- Extended real trace norm, §2.1, PDF p.4. The finite branch reuses the
accepted real-Hilbert modulus trace norm; non-trace-class operators have value ∞.
This extension is needed for cutoff errors and trace-norm difference quotients. -/
def realTraceSize (A : RealCoordinateOperator G) : ℝ≥0∞ :=
  if IsModulusTraceClass A then ENNReal.ofReal (modulusTraceNorm A) else ⊤

/-- Fredholm determinant det(I+A), given by its absolutely convergent principal-minor series
on the trace-class ideal. The empty principal minor contributes 1. -/
def fredholmPlus (A : RealCoordinateOperator G) : ℝ :=
  ∑' I : Finset G, (cylinderMatrix A I).det

/-- Finite coordinate projection in an arbitrary enumeration of the countable set. -/
def cutoffOperator (e : ℕ ≃ G) (n : ℕ) : RealCoordinateOperator G :=
  ∑ k ∈ Finset.range n,
    InnerProductSpace.rankOne ℝ (hilbertCoordinate (e k)) (hilbertCoordinate (e k))

/-- The corresponding genuine finite-coordinate quadratic polynomial. -/
def finiteQuadratic (e : ℕ ≃ G) (A : RealCoordinateOperator G) (n : ℕ) (x : CylinderPhase G) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    x (e i) * entry A (e i) (e j) * x (e j)

/-- A summably fast trace-norm approximation. For trace-class A this defining set is
nonempty. Fast cutoffs make the pointwise representative valid for every bounded
Gaussian covariance, including mutually singular limiting laws. -/
def quadraticCutoff (e : ℕ ≃ G) (A : RealCoordinateOperator G) (k : ℕ) : ℕ :=
  sInf {n | realTraceSize (A - cutoffOperator e n * A * cutoffOperator e n) ≤
    ENNReal.ofReal ((1 / 2 : ℝ) ^ k)}

/-- Canonical Gaussian quadratic observable: the almost sure, summably fast finite-coordinate
limit. It equals (x,Ax) on K. The zero fallback is used only when the real sequence has no limit. -/
def gaussianQuadratic (e : ℕ ≃ G) (A : RealCoordinateOperator G) (x : CylinderPhase G) : ℝ :=
  if h : ∃ a : ℝ, Tendsto
      (fun k => finiteQuadratic e A (quadraticCutoff e A k) x) atTop (𝓝 a) then
    Classical.choose h else 0

/-- Trace-norm differentiability, expressed without transporting an unaudited Banach instance. -/
def HasBilateralTraceDerivative (F : ℝ → RealCoordinateOperator G) (A : RealCoordinateOperator G) (t : ℝ) : Prop :=
  (∀ s, IsModulusTraceClass (F s)) ∧ IsModulusTraceClass A ∧
    Tendsto (fun s => realTraceSize ((s - t)⁻¹ • (F s - F t) - A)) (𝓝[≠] t) (𝓝 0)

/-- The precision increment T_t=D_t⁻¹-D⁻¹. -/
def precisionShift (D L : RealCoordinateOperator G) (t : ℝ) : RealCoordinateOperator G :=
  operatorInverse (covarianceAt D L t) - operatorInverse D

/-- Exactly (G1), differentiability at zero in the real trace norm, PDF p.5. -/
def G1 (D L : RealCoordinateOperator G) : Prop :=
  ∃ A, HasBilateralTraceDerivative (precisionShift D L) A 0

/-- The actual entropy-production operator, not a free derivative parameter, (8), PDF p.5. -/
def productionOperator (D L : RealCoordinateOperator G) : RealCoordinateOperator G :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.adjoint L * operatorInverse D + operatorInverse D * L)

/-- Entropy-production observable, with its actual Gaussian quadratic representative. -/
def production (e : ℕ ≃ G) (D L : RealCoordinateOperator G) (x : CylinderPhase G) : ℝ :=
  gaussianQuadratic e (productionOperator D L) x - basisOperatorTrace (D * productionOperator D L)

/-- Conversion to L¹, with no integrability hidden in its type. Integrability is stated
as a conclusion whenever this conversion is used. -/
def asL1 (mu : Measure (CylinderPhase G)) (f : CylinderPhase G → ℝ) : Lp ℝ 1 mu :=
  if h : MemLp f 1 mu then h.toLp f else 0

/-- The actual real Radon–Nikodym density, used only for the finite probability laws. -/
def realRNDensity (nu mu : Measure (CylinderPhase G)) (x : CylinderPhase G) : ℝ :=
  (nu.rnDeriv mu x).toReal

/-- For probabilities, a nonintegrable log density has entropy -∞. The AC guard
also gives -∞ for singular laws. Every density formula below separately states AC. -/
def nonpositiveRelativeEntropy (nu mu : Measure (CylinderPhase G)) : EReal :=
  if nu ≪ mu ∧ Integrable (fun x => Real.log (realRNDensity nu mu x)) nu then
    ((- ∫ x, Real.log (realRNDensity nu mu x) ∂nu : ℝ) : EReal) else ⊥

/-- Uniform coercive bounds for every real time, (G2), PDF p.6. -/
def G2 (D L : RealCoordinateOperator G) (m M : ℝ) : Prop :=
  0 < m ∧ m < M ∧ ∀ t v,
    m * ‖v‖ ^ 2 ≤ inner ℝ v (covarianceAt D L t v) ∧
    inner ℝ v (covarianceAt D L t v) ≤ M * ‖v‖ ^ 2

/-- (G3) requires actual strong limits in both time directions, PDF p.6. -/
def G3 (D L : RealCoordinateOperator G) : Prop :=
  (∃ A : RealCoordinateOperator G, ∀ v, Tendsto (fun t => covarianceAt D L t v) atTop (𝓝 (A v))) ∧
  (∃ A : RealCoordinateOperator G, ∀ v, Tendsto (fun t => covarianceAt D L t v) atBot (𝓝 (A v)))

/-- The constructed future covariance; uniqueness follows from strong convergence. -/
def futureCovariance (D L : RealCoordinateOperator G) : RealCoordinateOperator G :=
  if h : ∃ A : RealCoordinateOperator G, ∀ v,
      Tendsto (fun t => covarianceAt D L t v) atTop (𝓝 (A v)) then Classical.choose h else 0

/-- The constructed past covariance. -/
def pastCovariance (D L : RealCoordinateOperator G) : RealCoordinateOperator G :=
  if h : ∃ A : RealCoordinateOperator G, ∀ v,
      Tendsto (fun t => covarianceAt D L t v) atBot (𝓝 (A v)) then Classical.choose h else 0

/-- (G4), including a continuous action on the weighted Hilbert space. -/
def G4 (l : G → ℝ) (D L theta : RealCoordinateOperator G) : Prop :=
  (∀ v, ‖theta v‖ = ‖v‖) ∧ theta * theta = 1 ∧ WeightedCompatible l theta ∧
    theta * L = -(L * theta) ∧ theta * D = D * theta

/-- Coordinate action of time reversal, identity outside X_l. -/
def weightedTimeReversal (l : G → ℝ) (theta : RealCoordinateOperator G) (x : CylinderPhase G) : CylinderPhase G :=
  if inWeighted l x then weightedPhase l (weightedExtension l theta (weightedVector l x)) else x

/-- Logarithm retaining both infinite endpoints, §2.1, PDF pp.3–4. -/
def extendedProbabilityLog (x : ℝ≥0∞) : EReal :=
  if x = 0 then ⊥ else if x = ⊤ then ⊤ else (Real.log x.toReal : EReal)

/-- The actual finite-time reference-state Rényi functional (12), with divergent
moments assigned +∞ before any conversion to a real number. -/
def gaussianCumulant (D L : RealCoordinateOperator G) (t alpha : ℝ) : EReal :=
  extendedProbabilityLog (∫⁻ x, ENNReal.ofReal
    (Real.exp (alpha * Real.log (realRNDensity (cylinderGaussian (covarianceAt D L t)) (cylinderGaussian D) x)))
      ∂cylinderGaussian D)

/-- Real branch, used only locally inside the finite moment domain. -/
def realCumulant (D L : RealCoordinateOperator G) (t alpha : ℝ) : ℝ :=
  (gaussianCumulant D L t alpha).toReal

/-- Exact finite-time positivity domain J_t, PDF p.7. -/
def gaussianMomentDomain (D L : RealCoordinateOperator G) (t : ℝ) : Set ℝ :=
  {alpha | IsCovariance (operatorInverse D + alpha • precisionShift D L t)}

/-- The open minimal interval, as used in the proof, rather than an assertion that
endpoints cannot belong to the raw set-liminf, PDF p.7. -/
def minimalDomain (D L : RealCoordinateOperator G) : Set ℝ :=
  interior {alpha | ∃ T : ℝ, 0 < T ∧ ∀ t, T < t → alpha ∈ gaussianMomentDomain D L t}

/-- Jensen convexity for extended-real functions, with nonnegative real weights. -/
def ExtendedConvexOn (S : Set ℝ) (f : ℝ → EReal) : Prop :=
  Convex ℝ S ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ,
    0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a * x + b * y) ≤ (a : EReal) * f x + (b : EReal) * f y

/-- The two open half-planes together with the real interval S. -/
def gaussianCutPlane (S : Set ℝ) : Set ℂ :=
  {z | z.im ≠ 0 ∨ z.re ∈ S}

/-- The canonical logarithmic density (37), valid under all bounded Gaussian laws,
not an arbitrary version of the reference-measure RN derivative. -/
def canonicalLogDensity (e : ℕ ≃ G) (D L : RealCoordinateOperator G) (t : ℝ) (x : CylinderPhase G) : ℝ :=
  Real.log (fredholmPlus (D * precisionShift D L t)) / 2 -
    gaussianQuadratic e (precisionShift D L t) x / 2

/-- Actual NESS moment, §2.5, PDF p.9. -/
def nessCumulant (e : ℕ ≃ G) (D L : RealCoordinateOperator G) (t alpha : ℝ) : EReal :=
  extendedProbabilityLog (∫⁻ x, ENNReal.ofReal (Real.exp (-alpha * canonicalLogDensity e D L t x))
    ∂cylinderGaussian (futureCovariance D L))

/-- Exact NESS positivity domain (26). -/
def nessDomain (D L : RealCoordinateOperator G) (t : ℝ) : Set ℝ :=
  {alpha | IsCovariance (operatorInverse (futureCovariance D L) - alpha • precisionShift D L t)}

/-- Interior of the eventual NESS domains, exactly as in Theorem 2.6(3). -/
def minimalNessDomain (D L : RealCoordinateOperator G) : Set ℝ :=
  interior {alpha | ∃ T : ℝ, 0 < T ∧ ∀ t, T < t → alpha ∈ nessDomain D L t}

/-- A real limiting value; each result using this definition states actual convergence,
so the fallback does not assert existence of a limit. -/
def realLimit (f : ℝ → ℝ) : ℝ :=
  if h : ∃ a : ℝ, Tendsto f atTop (𝓝 a) then Classical.choose h else 0

/-- Asymptotic reference cumulant on its open finite domain. -/
def limitingCumulant (D L : RealCoordinateOperator G) (alpha : ℝ) : ℝ :=
  realLimit (fun t => t⁻¹ * realCumulant D L t alpha)

/-- Asymptotic NESS cumulant on its open finite domain. -/
def limitingNessCumulant (e : ℕ ≃ G) (D L : RealCoordinateOperator G) (alpha : ℝ) : ℝ :=
  realLimit (fun t => t⁻¹ * (nessCumulant e D L t alpha).toReal)

/-- Legendre–Fenchel transform with the source's sign and extended-real supremum. -/
def rateFunction (S : Set ℝ) (f : ℝ → ℝ) (s : ℝ) : EReal :=
  ⨆ alpha : {a : ℝ // -a ∈ S}, ((alpha.val * s - f (-alpha.val) : ℝ) : EReal)

/-- The time average of the actual evolved entropy-production observable. -/
def productionAverage (e : ℕ ≃ G) (l : G → ℝ) (D L : RealCoordinateOperator G)
    (t : ℝ) (x : CylinderPhase G) : ℝ :=
  t⁻¹ * ∫ s in (0 : ℝ)..t, production e D L (flow l L s x)

/-- Scaled log probability; zero probabilities give -∞, not Real.log 0. -/
def logEventRate (mu : Measure (CylinderPhase G)) (e : ℕ ≃ G) (l : G → ℝ)
    (D L : RealCoordinateOperator G) (t : ℝ) (U : Set ℝ) : EReal :=
  ((t⁻¹ : ℝ) : EReal) * extendedProbabilityLog (mu {x | productionAverage e l D L t x ∈ U})

/-- Jordan data for a possibly infinite-total-variation signed Borel measure.
Local finiteness and the weighted variation condition are imposed by LogPotential;
this is deliberately not Mathlib's finite SignedMeasure type. -/
structure SignedBorelPair where
  positive : Measure ℝ
  negative : Measure ℝ
  singular : positive.MutuallySingular negative

/-- Logarithmic potential (16), including integrability before real subtraction.
The support condition uses zero mass on the open interval, equivalently support
in its closed complement. -/
def LogPotential (J : Set ℝ) (f : ℝ → ℝ) (nu : SignedBorelPair) : Prop :=
  (nu.positive + nu.negative) J = 0 ∧
  (∀ K : Set ℝ, IsCompact K → (nu.positive + nu.negative) K < ⊤) ∧
  (∫⁻ r, (if r = 0 then ⊤ else ENNReal.ofReal |r|⁻¹) ∂(nu.positive + nu.negative)) < ⊤ ∧
  ∀ alpha ∈ J,
    (∀ᵐ r ∂(nu.positive + nu.negative), 0 < 1 - alpha / r) ∧
    Integrable (fun r => Real.log (1 - alpha / r)) nu.positive ∧
    Integrable (fun r => Real.log (1 - alpha / r)) nu.negative ∧
    f alpha = -(∫ r, Real.log (1 - alpha / r) ∂nu.positive) +
      ∫ r, Real.log (1 - alpha / r) ∂nu.negative

/-- Precision perturbation D^P=(D⁻¹+P)⁻¹, §2.6, PDF p.11. -/
def perturbedCovariance (D P : RealCoordinateOperator G) : RealCoordinateOperator G :=
  operatorInverse (operatorInverse D + P)

example (l : G → ℝ) (x : CylinderPhase G) : weightedDistance l x x = 0 := by
  simp [weightedDistance]

example (e : ℕ ≃ G) : cutoffOperator e 0 = 0 := by
  simp [cutoffOperator]

example (e : ℕ ≃ G) (A : RealCoordinateOperator G) (x : CylinderPhase G) : finiteQuadratic e A 0 x = 0 := by
  simp [finiteQuadratic]

example (l : G → ℝ) : weightedEnergy l (0 : CylinderPhase G) = 0 := by
  simp [weightedEnergy]

example : realTraceSize (0 : RealCoordinateOperator G) = 0 := by
  simp [realTraceSize, IsModulusTraceClass, modulusTraceNorm,
    QAlgorithms.Papers.Independent.Next46.P02.hilbertOperatorModulus,
    hilbertPositiveSqrt, QAlgorithms.Papers.Independent.Next46.P02.basisDiagonal]

example (e : ℕ ≃ G) (n : ℕ) (x : CylinderPhase G) : finiteQuadratic e (0 : RealCoordinateOperator G) n x = 0 := by
  simp [finiteQuadratic, entry]

example : extendedProbabilityLog 0 = ⊥ := by
  simp [extendedProbabilityLog]

example : extendedProbabilityLog ⊤ = ⊤ := by
  simp [extendedProbabilityLog]

end QAlgorithms.Papers.Independent.Intake100.P97


