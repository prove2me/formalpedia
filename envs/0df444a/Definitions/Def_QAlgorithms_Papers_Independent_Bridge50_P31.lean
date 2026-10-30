-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31
-- name    : QAlgorithms_Papers_Independent_Bridge50_P31
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T15:37:00.314615+00:00
-- url     : https://prove2.me/theorems/eaa82e0c-efbc-4de0-840e-5e9eb0e70c27
-- title:
--   Definitions for Reversibility conditions for quantum operations
-- statement:
--   The objects the formalized statements of *Reversibility conditions for quantum operations* (arXiv:1107.0453) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FaithfulOn`: PDF p.3: faithful on the positive cone, not injective on every operator.
--   - `supportCorner`: PDF pp.3,10: the corner pAp as an ambient set; its unit is p. This is unrelated to the accepted HybridSource.corner rate vector.
--   - `SchwarzOn`: PDF p.4, (1): Schwarz means coefficient exactly one.
--   - `UnitalSchwarzOn`: PDF pp.6,9: unitality uses the actual domain and codomain units.
--   - `SandwichDefined`: PDF p.4: the singular sandwich is defined exactly on the range of c.
--   - `generalizedSandwich`: PDF pp.4–5: a* c^+ a with the range condition kept separately. Accepted functions called sandwich implement different products or supermaps.
--   - `GeneralizedSchwarz`: PDF p.5, (2): generalized Schwarz inequality at a positive invertible c.
--   - `stateDual`: PDF p.6: computed forward state dual, with support inverses. Its intrinsic restriction is pAp -> p0Bp0. The full-space expression is only an ambient extension.
--   - `algebraMultiplicativeDomain`: PDF p.7: both Schwarz equalities in the actual algebra domain. Accepted Dependency50.P37.multiplicativeDomain tests all ambient inputs.
--   - `fixedPoints`: PDF p.7: fixed points in the actual domain algebra.
--   - `recoveryComposite`: PDF pp.8,13: Phi=T* o T_rho, computed from T and rho. Accepted Dependency50.P28.phi is a scalar convex conjugate, not this map.
--   - `phiTilde`: PDF p.8: Phi-tilde=T_rho o T*, computed from T and rho.
--   - `IsStarAlgebraSet`: PDF p.7: being an actual unital star subalgebra, without assuming this property when the set of fixed points is first defined.
--   - `MapRanges`: Canonical ambient extension of an intrinsic map between possibly nonunital corners, PDF pp.7,10. Both range conditions fix the trace-orthogonal extensions.
--   - `ConditionalExpectation`: PDF p.7: positive bimodule projection onto the named subalgebra.
--   - `traceConditionalExpectation`: PDF p.7: the unique representation-trace-preserving conditional expectation. Choice is from its defining property, never from a recovery conclusion. Accepted Renew46.P24.traceExpectation is a scalar state functional.
--   - `FaithfulTraceOn`: PDF p.7: a faithful trace on C, with no normalization condition. Values of tau off C are immaterial, so any complex-linear ambient extension represents it.
--   - `restrictionDensity`: PDF p.7: density of the restricted state with respect to the specified trace. This is the unique element satisfying the displayed trace pairing.
--   - `StarIsoOn`: PDF p.8: the restriction of T is a star isomorphism, inverse U. Linearity is inherited from the computed maps in the statements.
--   - `FamilyReversible`: PDF p.9, (5): one complex-linear recovery, with unital Schwarz adjoint, works on the entire family. The accepted Support50.P12.Reversible treats a pair; pairwise witnesses cannot replace this common family witness.
--   - `Conditions`: PDF p.9: the two standing conditions, retaining rho in S and both computed unital Schwarz maps. No complete positivity premise is substituted.
--   - `AlgebraChannel`: PDF p.13, (v),(vi): a completely positive trace-preserving intrinsic map. Unlike accepted full-matrix CPTP predicates, its properties are tested on A.
--   - `derivative`: PDF p.12: commutant Radon–Nikodym derivative, computed on the support.
--   - `weightedPair`: PDF p.5: the rho-weighted sesquilinear form is conjugate-linear first.
--   - `saturation`: PDF pp.14,17: the union over ALL real modular translates.
--   - `NormCriterion`: PDF pp.19–20: norm preservation at all nonnegative thresholds.
--   - `positiveTest`: PDF pp.17–18: strictly positive projection, defined also for negative t.
--   - `kernelTest`: PDF pp.17–18: full kernel projection, retaining all zero eigenvalue ties.
--   - `resolvent`: PDF p.23: resolvent of L_a + s R_b, by its genuine two-sided spectral calculus. On faithful a,b and s>=0 every denominator is strictly positive.
--   - `inverseMetric`: PDF pp.23–25: inverse of J_rho^f=f(L_rho R_rho^-1)R_rho.
--   - `metric`: PDF p.23: the monotone metric on self-adjoint tangent vectors.
--   - `chiSquared`: PDF p.23: chi-squared divergence uses the difference of the two states.
--   - `MetricGenerator`: PDF p.23: positive symmetric operator monotone generator; normalization f(1)=1 is imposed only when calling the metric a Fisher information.
--   - `InverseRepresentation`: PDF p.23, corrected representation: the finite-parameter Stieltjes part of 1/f, with its nonnegative constant separated. The printed formula omits that constant (e.g. harmonic f). This correction needs independent moderation.
--   - `inverseMeasure`: PDF pp.23–25: the actual finite-parameter representing measure of 1/f. No arbitrary measure is admitted as a rich-support witness.
--   - `MetricRich`: PDF pp.24–25: cardinal comparison, allowing infinite measure support.
--   - `Tangent`: PDF p.24: tangent vectors are self-adjoint and traceless.
--   - `affineFamily`: PDF p.24: maximal affine state family, INCLUDING its boundary states.
--   - `familySpan`: PDF p.24: REAL span of pairwise differences in the family.
--   - `projectionExampleReference`: PDF p.11: the actual matrix rho in Example 1. Accepted Support50.P12.exampleRho is a different fixed 3-by-3 matrix.
--   - `extendRecovery`: PDF p.10: the map extending a corner recovery; the complement is weighted by the representation trace and the reference state.
--   - `CornerReversible`: PDF p.10: reversibility between genuine support corners.
--   - `CornerKPositive`: PDF p.10: n-positivity on a support corner uses genuine n-by-n blocks.
--   - `FiniteMixture`: PDF p.9: membership in the FINITE convex hull, without taking a closure.
--   - `inverseRestriction`: PDF pp.13–14: inverse of the faithful restriction of T* on its multiplicative domain, extended canonically. Choice uses only the inverse identities.
--   - `recoveryAlgebra`: PDF p.13: A1 is the subalgebra generated by modular derivatives of S.
--   - `structuralRecovery`: PDF pp.13–14: the proof's actual E_rho* o R* o F recovery.
--   - `faithfulRate`: PDF p.22, Remark 3: the nonempty-case entropy infimum, with an explicit positive choice for the trivial empty auxiliary family. EReal retains the infimum until its nonempty finite value is converted to a real.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, https://arxiv.org/abs/1107.0453v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

/-! Jencova, Reversibility conditions for quantum operations, arXiv:1107.0453v2.
All page numbers are PDF pages. Representation traces are unnormalized and all
maps are complex linear. An intrinsic algebra map is represented by its canonical
trace-orthogonal full-matrix extension (`AlgebraExtension`). Local definitions
below use actual matrices and computed support inverses. Compilation is pending
batch handoff. The unqualified n-positivity claim on p.6 is deferred in HARD.md. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P31

open Filter MeasureTheory Set
open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)
open QAlgorithms.Papers.Independent.Dependency50.P21
  (channelAdjoint spectralFunction petz relativeEntropy)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Next46.P23 (Supports matrixCommutant)
open QAlgorithms.Papers.Independent.Support50.P12
  (Alg AlgebraDensity AlgebraExtension PositiveOnConcreteAlgebra AlgebraTracePreserving
   AlgebraKPositive AlgebraCompletelyPositive supp spec cpow quasi hull modularSpec)
open QAlgorithms.Papers.Independent.Information100.P50 (OperatorMonotone)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.3: faithful on the positive cone, not injective on every operator. -/
def FaithfulOn (A : Set (Mat I)) (T : Mat I → Mat J) : Prop :=
  ∀ a ∈ A, a.PosSemidef → T a = 0 → a = 0

/-- PDF pp.3,10: the corner pAp as an ambient set; its unit is p.
This is unrelated to the accepted HybridSource.corner rate vector. -/
def supportCorner (A : Set (Mat I)) (p : Mat I) : Set (Mat I) :=
  {a | a ∈ A ∧ p * a * p = a}

/-- PDF p.4, (1): Schwarz means coefficient exactly one. -/
def SchwarzOn (A : Set (Mat I)) (T : Mat I → Mat J) : Prop :=
  ∀ a ∈ A, LE ((T a)ᴴ * T a) (T (aᴴ * a))

/-- PDF pp.6,9: unitality uses the actual domain and codomain units. -/
def UnitalSchwarzOn (A : Set (Mat I)) (eA : Mat I) (eB : Mat J)
    (T : Mat I → Mat J) : Prop := T eA = eB ∧ SchwarzOn A T

/-- PDF p.4: the singular sandwich is defined exactly on the range of c. -/
def SandwichDefined (c a : Mat I) : Prop :=
  LinearMap.range a.mulVecLin ≤ LinearMap.range c.mulVecLin

/-- PDF pp.4–5: a* c^+ a with the range condition kept separately.
Accepted functions called sandwich implement different products or supermaps. -/
def generalizedSandwich (c a : Mat I) : Mat I := aᴴ * supportPower c (-1) * a

/-- PDF p.5, (2): generalized Schwarz inequality at a positive invertible c. -/
def GeneralizedSchwarz (A : Set (Mat I)) (T : Mat I → Mat J) (c : Mat I) : Prop :=
  ∀ a ∈ A, SandwichDefined (T c) (T a) ∧ LE (generalizedSandwich (T c) (T a)) (T (generalizedSandwich c a))

/-- PDF p.6: computed forward state dual, with support inverses. Its intrinsic
restriction is pAp -> p0Bp0. The full-space expression is only an ambient extension. -/
def stateDual (T : Mat I → Mat J) (rho a : Mat I) : Mat J :=
  supportPower (T rho) (-(1 / 2)) *
    T (supportPower rho (1 / 2) * a * supportPower rho (1 / 2)) *
    supportPower (T rho) (-(1 / 2))

/-- PDF p.7: both Schwarz equalities in the actual algebra domain.
Accepted Dependency50.P37.multiplicativeDomain tests all ambient inputs. -/
def algebraMultiplicativeDomain (A : Set (Mat I)) (T : Mat I → Mat J) : Set (Mat I) :=
  {a | a ∈ A ∧ T (aᴴ * a) = (T a)ᴴ * T a ∧ T (a * aᴴ) = T a * (T a)ᴴ}

/-- PDF p.7: fixed points in the actual domain algebra. -/
def fixedPoints (A : Set (Mat I)) (Phi : Mat I → Mat I) : Set (Mat I) :=
  {a | a ∈ A ∧ Phi a = a}

/-- PDF pp.8,13: Phi=T* o T_rho, computed from T and rho.
Accepted Dependency50.P28.phi is a scalar convex conjugate, not this map. -/
def recoveryComposite (T : Mat I → Mat J) (rho a : Mat I) : Mat I :=
  channelAdjoint T (stateDual T rho a)

/-- PDF p.8: Phi-tilde=T_rho o T*, computed from T and rho. -/
def phiTilde (T : Mat I → Mat J) (rho : Mat I) (b : Mat J) : Mat J :=
  stateDual T rho (channelAdjoint T b)

/-- PDF p.7: being an actual unital star subalgebra, without assuming this
property when the set of fixed points is first defined. -/
def IsStarAlgebraSet (C : Set (Mat I)) : Prop :=
  ∃ D : Alg I, (D : Set (Mat I)) = C

/-- Canonical ambient extension of an intrinsic map between possibly nonunital
corners, PDF pp.7,10. Both range conditions fix the trace-orthogonal extensions. -/
def MapRanges (A : Set (Mat I)) (B : Set (Mat J)) (T : Mat I → Mat J) : Prop :=
  (∀ a, T a ∈ B) ∧ (∀ b, channelAdjoint T b ∈ A)

/-- PDF p.7: positive bimodule projection onto the named subalgebra. -/
def ConditionalExpectation (A C : Set (Mat I)) (E : MatrixMap I I) : Prop :=
  MapRanges A C E ∧ (∀ a ∈ A, a.PosSemidef → (E a).PosSemidef) ∧
  (∀ c ∈ C, E c = c) ∧
  ∀ a ∈ A, ∀ b ∈ C, ∀ c ∈ C, E (b * a * c) = b * E a * c

/-- PDF p.7: the unique representation-trace-preserving conditional expectation.
Choice is from its defining property, never from a recovery conclusion.
Accepted Renew46.P24.traceExpectation is a scalar state functional. -/
def traceConditionalExpectation (A C : Set (Mat I)) : MatrixMap I I :=
  Classical.epsilon (fun E => ConditionalExpectation A C E ∧ ∀ a ∈ A, (E a).trace = a.trace)

/-- PDF p.7: a faithful trace on C, with no normalization condition. Values of
tau off C are immaterial, so any complex-linear ambient extension represents it. -/
def FaithfulTraceOn (C : Set (Mat I)) (tau : Mat I →ₗ[ℂ] ℂ) : Prop :=
  (∀ a ∈ C, a.PosSemidef → (tau a).im = 0 ∧ 0 ≤ (tau a).re) ∧
  (∀ a ∈ C, a.PosSemidef → tau a = 0 → a = 0) ∧
  ∀ a ∈ C, ∀ b ∈ C, tau (a * b) = tau (b * a)

/-- PDF p.7: density of the restricted state with respect to the specified trace.
This is the unique element satisfying the displayed trace pairing. -/
def restrictionDensity (C : Set (Mat I)) (tau : Mat I →ₗ[ℂ] ℂ) (rho : Mat I) : Mat I :=
  Classical.epsilon (fun d => d ∈ C ∧ d.PosSemidef ∧ ∀ a ∈ C, tau (a * d) = (rho * a).trace)

/-- PDF p.8: the restriction of T is a star isomorphism, inverse U.
Linearity is inherited from the computed maps in the statements. -/
def StarIsoOn (C : Set (Mat I)) (D : Set (Mat J))
    (T : Mat I → Mat J) (U : Mat J → Mat I) : Prop :=
  (∀ a ∈ C, T a ∈ D ∧ U (T a) = a) ∧
  (∀ b ∈ D, U b ∈ C ∧ T (U b) = b) ∧
  (∀ a ∈ C, T (aᴴ) = (T a)ᴴ) ∧
  ∀ a ∈ C, ∀ b ∈ C, T (a * b) = T a * T b

/-- PDF p.9, (5): one complex-linear recovery, with unital Schwarz adjoint,
works on the entire family. The accepted Support50.P12.Reversible treats
a pair; pairwise witnesses cannot replace this common family witness. -/
def FamilyReversible (A : Alg I) (B : Alg J) (T : MatrixMap I J) (S : Set (Mat I)) : Prop :=
  ∃ R : MatrixMap J I, AlgebraExtension B A R ∧
    UnitalSchwarzOn A 1 1 (channelAdjoint R) ∧ ∀ sigma ∈ S, R (T sigma) = sigma

/-- PDF p.9: the two standing conditions, retaining rho in S and both computed
unital Schwarz maps. No complete positivity premise is substituted. -/
def Conditions (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) : Prop :=
  AlgebraExtension A B T ∧ (∀ sigma ∈ S, AlgebraDensity A sigma) ∧
  rho ∈ S ∧ rho.PosDef ∧ (T rho).PosDef ∧
  UnitalSchwarzOn B 1 1 (channelAdjoint T) ∧ UnitalSchwarzOn A 1 1 (stateDual T rho)

/-- PDF p.13, (v),(vi): a completely positive trace-preserving intrinsic map.
Unlike accepted full-matrix CPTP predicates, its properties are tested on A. -/
def AlgebraChannel (A : Alg I) (B : Alg J) (T : MatrixMap I J) : Prop :=
  AlgebraExtension A B T ∧ AlgebraTracePreserving A T ∧ AlgebraCompletelyPositive A T

/-- PDF p.12: commutant Radon–Nikodym derivative, computed on the support. -/
def derivative (sigma rho : Mat I) : Mat I :=
  supportPower rho (-(1 / 2)) * sigma * supportPower rho (-(1 / 2))

/-- PDF p.5: the rho-weighted sesquilinear form is conjugate-linear first. -/
def weightedPair (rho a b : Mat I) : ℂ :=
  (aᴴ * supportPower rho (1 / 2) * b * supportPower rho (1 / 2)).trace

/-- PDF pp.14,17: the union over ALL real modular translates. -/
def saturation (rho : Mat I) (S : Set (Mat I)) : Set (Mat I) :=
  {a | ∃ sigma ∈ S, ∃ t : ℝ, a = cpow rho (Complex.I * (t : ℂ)) * sigma *
    cpow rho (-Complex.I * (t : ℂ))}

/-- PDF pp.19–20: norm preservation at all nonnegative thresholds. -/
def NormCriterion (T : Mat I → Mat J) (rho : Mat I) (S : Set (Mat I)) : Prop :=
  ∀ sigma ∈ S, ∀ t : ℝ, 0 ≤ t →
    QAlgorithms.traceNorm (sigma - (t : ℂ) • rho) =
      QAlgorithms.traceNorm (T sigma - (t : ℂ) • T rho)

/-- PDF pp.17–18: strictly positive projection, defined also for negative t. -/
def positiveTest (sigma rho : Mat I) (t : ℝ) : Mat I :=
  supp (QAlgorithms.Papers.Independent.Information100.P07.positivePart (sigma - (t : ℂ) • rho))

/-- PDF pp.17–18: full kernel projection, retaining all zero eigenvalue ties. -/
def kernelTest (sigma rho : Mat I) (t : ℝ) : Mat I :=
  QAlgorithms.spectralProjector (sigma - (t : ℂ) • rho) 0

/-- PDF p.23: resolvent of L_a + s R_b, by its genuine two-sided spectral
calculus. On faithful a,b and s>=0 every denominator is strictly positive. -/
def resolvent (a b : Mat I) (s : ℝ) (x : Mat I) : Mat I :=
  ∑ u ∈ spec a, ∑ v ∈ spec b,
    (((u + s * v)⁻¹ : ℝ) : ℂ) • (QAlgorithms.spectralProjector a u * x * QAlgorithms.spectralProjector b v)

/-- PDF pp.23–25: inverse of J_rho^f=f(L_rho R_rho^-1)R_rho. -/
def inverseMetric (f : ℝ → ℝ) (rho x : Mat I) : Mat I :=
  ∑ u ∈ spec rho, ∑ v ∈ spec rho,
    (((v * f (u / v))⁻¹ : ℝ) : ℂ) •
      (QAlgorithms.spectralProjector rho u * x * QAlgorithms.spectralProjector rho v)

/-- PDF p.23: the monotone metric on self-adjoint tangent vectors. -/
def metric (f : ℝ → ℝ) (rho x y : Mat I) : ℝ := tr (inverseMetric f rho x * y)

/-- PDF p.23: chi-squared divergence uses the difference of the two states. -/
def chiSquared (f : ℝ → ℝ) (sigma rho : Mat I) : ℝ := metric f rho (sigma - rho) (sigma - rho)

/-- PDF p.23: positive symmetric operator monotone generator; normalization
f(1)=1 is imposed only when calling the metric a Fisher information. -/
def MetricGenerator (f : ℝ → ℝ) : Prop :=
  OperatorMonotone f ∧ (∀ t : ℝ, 0 < t → 0 < f t) ∧
  ∀ t : ℝ, 0 < t → f t = t * f (t⁻¹)

/-- PDF p.23, corrected representation: the finite-parameter Stieltjes part
of 1/f, with its nonnegative constant separated. The printed formula omits that
constant (e.g. harmonic f). This correction needs independent moderation. -/
def InverseRepresentation (f : ℝ → ℝ) (a : ℝ) (nu : Measure ℝ) : Prop :=
  0 ≤ a ∧ nu (Iio 0) = 0 ∧
  Integrable (fun s : ℝ => (1 + s ^ 2)⁻¹) nu ∧
  Integrable (fun s : ℝ => s / (1 + s ^ 2)) nu ∧
  ∀ t : ℝ, 0 < t → Integrable (fun s : ℝ => (s + t)⁻¹) nu ∧
    (f t)⁻¹ = a + ∫ s, (s + t)⁻¹ ∂nu

/-- PDF pp.23–25: the actual finite-parameter representing measure of 1/f.
No arbitrary measure is admitted as a rich-support witness. -/
def inverseMeasure (f : ℝ → ℝ) : Measure ℝ :=
  Classical.epsilon (fun nu => ∃ a : ℝ, InverseRepresentation f a nu)

/-- PDF pp.24–25: cardinal comparison, allowing infinite measure support. -/
def MetricRich (f : ℝ → ℝ) (n : ℕ) : Prop :=
  (n : Cardinal) ≤ Cardinal.mk (inverseMeasure f).support

/-- PDF p.24: tangent vectors are self-adjoint and traceless. -/
def Tangent (A : Alg I) (x : Mat I) : Prop := x ∈ A ∧ x.IsHermitian ∧ x.trace = 0

/-- PDF p.24: maximal affine state family, INCLUDING its boundary states. -/
def affineFamily (A : Alg I) (rho x : Mat I) : Set (Mat I) :=
  {sigma | AlgebraDensity A sigma ∧ ∃ u : ℝ, sigma = rho + (u : ℂ) • x}

/-- PDF p.24: REAL span of pairwise differences in the family. -/
def familySpan (S : Set (Mat I)) : Submodule ℝ (Mat I) :=
  Submodule.span ℝ {x | ∃ a ∈ S, ∃ b ∈ S, x = a - b}

/-- PDF p.11: the actual matrix rho in Example 1.
Accepted Support50.P12.exampleRho is a different fixed 3-by-3 matrix. -/
def projectionExampleReference (sigma p : Mat I) : Mat I :=
  let lam := tr (p * sigma)
  let x := ((1 - lam : ℝ) : ℂ) • p + (lam : ℂ) • (1 - p)
  (1 - x)⁻¹ * sigma * x

/-- PDF p.10: the map extending a corner recovery; the complement is weighted
by the representation trace and the reference state. -/
def extendRecovery (R : Mat J → Mat I) (p0 : Mat J) (rho : Mat I) (b : Mat J) : Mat I :=
  R (p0 * b * p0) + (b * (1 - p0)).trace • rho

/-- PDF p.10: reversibility between genuine support corners. -/
def CornerReversible (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (p : Mat I) (p0 : Mat J) : Prop :=
  ∃ R : MatrixMap J I, MapRanges (supportCorner B p0) (supportCorner A p) R ∧
    UnitalSchwarzOn (supportCorner A p) p p0 (channelAdjoint R) ∧
    ∀ sigma ∈ S, R (T sigma) = sigma

/-- PDF p.10: n-positivity on a support corner uses genuine n-by-n blocks. -/
def CornerKPositive (A : Alg I) (p : Mat I) (T : Mat I → Mat J) (n : ℕ) : Prop :=
  ∀ X : Mat (Fin n × I), (∀ a b, (fun i j => X (a, i) (b, j)) ∈ supportCorner A p) →
    X.PosSemidef → (QAlgorithms.Papers.Independent.Support50.P12.amp T n X).PosSemidef

/-- PDF p.9: membership in the FINITE convex hull, without taking a closure. -/
def FiniteMixture (S : Set (Mat I)) (rho : Mat I) : Prop :=
  ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ a : Fin n → Mat I,
    (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, a k ∈ S) ∧
    rho = ∑ k, (w k : ℂ) • a k

/-- PDF pp.13–14: inverse of the faithful restriction of T* on its multiplicative
domain, extended canonically. Choice uses only the inverse identities. -/
def inverseRestriction (T : Mat I → Mat J) (C : Set (Mat I)) (D : Set (Mat J)) : MatrixMap J I :=
  Classical.epsilon (fun R => MapRanges D C R ∧ ∀ x ∈ C, R (T x) = x)

/-- PDF p.13: A1 is the subalgebra generated by modular derivatives of S. -/
def recoveryAlgebra (rho : Mat I) (S : Set (Mat I)) : Alg I :=
  StarAlgebra.adjoin ℂ (saturation rho ((fun sigma => derivative sigma rho) '' S))

/-- PDF pp.13–14: the proof's actual E_rho* o R* o F recovery. -/
def structuralRecovery (A : Alg I) (B : Alg J) (T : MatrixMap I J)
    (S : Set (Mat I)) (rho : Mat I) (b : Mat J) : Mat I :=
  let C : Set (Mat I) := recoveryAlgebra rho S
  let D := algebraMultiplicativeDomain B (channelAdjoint T)
  let E := traceConditionalExpectation A C
  let F := traceConditionalExpectation B D
  let R := inverseRestriction (channelAdjoint T) D (channelAdjoint T '' D)
  channelAdjoint (stateDual E rho) (channelAdjoint R (F b))

/-- The inverse-on-support sandwich vanishes at a zero argument. -/
example (rho : Mat I) : derivative 0 rho = 0 := by simp [derivative]

/-- The empty family has empty modular saturation. -/
example (rho : Mat I) : saturation rho ∅ = ∅ := by
  ext a
  simp [saturation]

/-- A zero tangent direction gives zero chi-squared distance. -/
example (f : ℝ → ℝ) (rho : Mat I) : chiSquared f rho rho = 0 := by
  simp [chiSquared, metric, inverseMetric, tr]

/-- The support-corner definition uses its own projection as unit. -/
example (A : Set (Mat I)) (a : Mat I) : a ∈ supportCorner A 1 ↔ a ∈ A := by
  simp [supportCorner]

/-- Positive and kernel tests are defined on the negative half-line too. -/
example (sigma rho : Mat I) : kernelTest sigma rho (-1) =
    QAlgorithms.spectralProjector (sigma + rho) 0 := by simp [kernelTest]

/-- A zero linear map gives a zero forward dual, including singular reference. -/
example (rho a : Mat I) : stateDual (0 : MatrixMap I J) rho a = 0 := by
  simp [stateDual]

/-- The identity fixes the whole actual domain, including scalar algebras. -/
example (A : Set (Mat I)) : fixedPoints A (fun a => a) = A := by
  ext a
  simp [fixedPoints]

/-- Resolvents and the metric inverse act linearly at the zero vector. -/
example (a b : Mat I) (s : ℝ) : resolvent a b s 0 = 0 := by
  simp [resolvent]

/-- A vanished complement introduces no spurious trace contribution. -/
example (R : Mat J → Mat I) (rho : Mat I) (b : Mat J) :
    extendRecovery R 1 rho b = R b := by
  simp [extendRecovery]

/-- PDF p.22, Remark 3: the nonempty-case entropy infimum, with an explicit
positive choice for the trivial empty auxiliary family. EReal retains the
infimum until its nonempty finite value is converted to a real. -/
def faithfulRate (T : Mat I → Mat J) (rho : Mat I) (S0 : Set (Mat I)) : ℝ :=
  if S0.Nonempty then
    (sInf ((fun sigma => relativeEntropy (T rho) (T sigma)) '' S0)).toReal
  else 1

/-- Empty auxiliary family: a positive rate is supplied without an empty real infimum. -/
example (T : Mat I → Mat J) (rho : Mat I) : faithfulRate T rho ∅ = 1 := by
  simp [faithfulRate]

end QAlgorithms.Papers.Independent.Bridge50.P31


