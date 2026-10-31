-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P41
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:30:41.432769+00:00
-- url     : https://prove2.me/theorems/9b3819d5-b5dc-4d6a-be15-7310a5ac5ab2
-- title:
--   Definitions for Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators
-- statement:
--   The objects the formalized statements of *Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators* (arXiv:math/9806031) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AngularCircle`: Angular circle, with coordinate θ modulo 2π (§4, PDF pp.10–11).
--   - `angularHaar`: Normalized angular Haar measure, of total mass one (§14, PDF p.20).
--   - `CircleL2`: Actual vector-valued L² classes, with the Euclidean norm on C^N (§14, p.20).
--   - `vectorMonomial`: Continuous nonnegative Fourier monomial θ ↦ exp(inθ)v (§4, pp.10–11).
--   - `vectorMonomialL2`: The same Fourier monomial as an L² class (§4, pp.10–11).
--   - `circleHardySpace`: Hilbert-closed span of all z^n v, n ≥ 0, not a smooth-function space (§14, p.20).
--   - `angularArc`: Nonempty proper open arcs are obtained from a < b < a+2π (§14, p.20). The real endpoints are retained, so arcs crossing θ=0 are also allowed.
--   - `VanishesOnArc`: Vanishing on an arc means Haar-a.e. vanishing of an L² representative (§14, p.20).
--   - `linearRankOneMatrix`: Rank-one operator Q(x)=φ(x)v (§18, PDF p.25). This allows an arbitrary complex-linear functional φ; the frozen Advance50.P38.rankOneMatrix instead denotes the Hermitian operator xx* and cannot represent this source's general rank-one operator.
--   - `resolventScalar`: Resolvent scalar χ_A(t)=1+φ((tI−A)⁻¹v) (§22, PDF p.28). Theorems evaluating it require the resolvent matrix to be invertible.
--   - `BasicODEData`: The actual normalized spectral data of the basic ODE (§18, PDF p.25). Both P and R=Q−P have simple nonresonant spectra and are in general position with Q=vφ; mu records the eigenvalues of P−Q, not those of R.
--   - `frobeniusPair`: Recursive Frobenius coefficients and their partial sums (§22, PDF p.28). The pair is (ξ_n, ξ_0+⋯+ξ_n), constructed from the ODE recurrence. Nonresonance supplies every inverse at positive n in its applications.
--   - `projectedCoefficient`: α_{i,n}=φ(ξ_{i,0}+⋯+ξ_{i,n}) from the constructed Frobenius solution (§22, p.28).
--   - `IntegerSignature`: Unnormalized integer signatures, before common-shift SU(N) equivalence (§2, p.8). The frozen Dependency50.P26.Signature describes quantum-comb wire dimensions; it is unrelated to these integer highest-weight coordinates.
--   - `IsSignature`: A signature is weakly decreasing (§2, PDF p.8).
--   - `IsPermissible`: Level-permissibility, expressed without artificial zero-padding (§§9,34, pp.16,43).
--   - `AddsOneBox`: Adding one actual box before renormalizing signatures (§2, p.8).
--   - `BoxPath`: A path retains every intermediate permissible signature (§32, pp.40–42).
--   - `AdjacentPaths`: Adjacent paths differ at exactly one interior signature (§32, PDF pp.41–42).
--   - `AffineWeylElement`: An element of Λ₀⋊S_N, with translation (N+ℓ)m and Σm_i=0 (§34, PDF p.43).
--   - `affineAction`: Coordinate action with the usual inverse-permutation convention (§34, p.43).
--   - `HasTrivialStabilizer`: Trivial stabilizer in the actual affine action (§34, PDF p.43).
--   - `weylShift`: The source's Weyl shift δ=(N−1,…,0), with zero-based Lean indices (§34, p.43).
--   - `InAffineRootLattice`: Root-lattice membership uses zero-sum integral translations, not arbitrary shifts (§34, p.43).
--   - `gaugeParameterSet`: The nonresonant parameter set for a holomorphic family B=zA (§19, PDF p.26). Zero eigenvalue differences are allowed; only positive integral differences are excluded.
--   - `gaugeDomain`: Holomorphic gauge domain including z=0 (§19, PDF p.26).
--   - `IsNormalizedGauge`: A normalized holomorphic invertible matrix gauge; its equation is imposed only for 0<|z|<R (§19, PDF p.26). Values outside the domain play no role.
--   - `companionMatrix`: Companion matrix with superdiagonal ones and last row a (§20, PDF pp.26–27).
--   - `lastRowMatrix`: The simultaneous rank-one form has only its last row nonzero (§20, pp.26–27).
--   - `companionPolynomial`: Polynomial a(t)=t^d−Σa_i t^(i−1), with zero-based Fin indices (§20, p.27).
--   - `rowPolynomial`: Polynomial b(t)=Σb_i t^(i−1) (§20, PDF p.27).
--   - `NoCommonRoot`: No common complex root, not merely inequality of the two polynomials (§20, p.27).
--   - `HasSimpleSpectrum`: Simple spectrum includes a full eigenbasis (§§18,20, PDF pp.25–27).
--   - `RankOneGeneralPosition`: Both-sided general position for a simple-spectrum P and rank-one Q: Q annihilates no eigenline and its range has no zero eigenbasis coordinate (§20, p.26).
--   - `realAffineAction`: Real affine action, on all R^N rather than a zero-sum slice (§34, PDF p.43).
--   - `IsRealRootTranslation`: Real zero-sum root-lattice translations (§34, PDF p.43).
--   - `HasTrivialRealStabilizer`: Trivial stabilizer in the real affine action (§34, PDF p.43).
--   - `translationAlcove`: The symmetric closed translation domain (§34 lemma (a), PDF p.43).
--   - `dominantAlcove`: The closed dominant affine alcove (§34 lemma (b), PDF p.43).
--   - `IsTranslationFundamentalDomain`: Closed fundamental domain: orbit coverage and no overlap of interiors under nonidentity translations. Boundary duplicates are allowed (§34, PDF p.43).
--   - `IsAffineFundamentalDomain`: Closed fundamental domain for the affine Weyl action (§34, PDF p.43).
--   - `IsCyclicFor`: Cyclicity uses the norm-dense actual operator orbit MΩ (§12, PDF p.18).
--   - `closedSelfAdjointRealPart`: K is the real closed span of self-adjoint vectors aΩ (§12, PDF p.18). This does not assume standardness or any modular identities.
--   - `imaginaryRealPart`: The real subspace iK uses the original complex structure (§12, PDF p.18).
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, https://arxiv.org/abs/math/9806031v1

import Mathlib

/-!
Statements from Antony Wassermann, arXiv:math/9806031v1.
All constructions below are local to this paper. Analytic representation-theoretic
nodes needing further substrate are explicitly inventoried in HARD.md.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- Angular circle, with coordinate θ modulo 2π (§4, PDF pp.10–11). -/
abbrev AngularCircle := AddCircle (2 * Real.pi)

instance angularPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- Normalized angular Haar measure, of total mass one (§14, PDF p.20). -/
abbrev angularHaar : Measure AngularCircle := AddCircle.haarAddCircle

/-- Actual vector-valued L² classes, with the Euclidean norm on C^N (§14, p.20). -/
abbrev CircleL2 (N : ℕ) := Lp (EuclideanSpace ℂ (Fin N)) 2 angularHaar

/-- Continuous nonnegative Fourier monomial θ ↦ exp(inθ)v (§4, pp.10–11). -/
def vectorMonomial (N n : ℕ) (v : EuclideanSpace ℂ (Fin N)) :
    C(AngularCircle, EuclideanSpace ℂ (Fin N)) where
  toFun θ := fourier (T := 2 * Real.pi) (n : ℤ) θ • v
  continuous_toFun := (fourier (T := 2 * Real.pi) (n : ℤ)).continuous.smul continuous_const

/-- The same Fourier monomial as an L² class (§4, pp.10–11). -/
def vectorMonomialL2 (N n : ℕ) (v : EuclideanSpace ℂ (Fin N)) : CircleL2 N :=
  ContinuousMap.toLp 2 angularHaar ℂ (vectorMonomial N n v)

/-- Hilbert-closed span of all z^n v, n ≥ 0, not a smooth-function space (§14, p.20). -/
def circleHardySpace (N : ℕ) : Submodule ℂ (CircleL2 N) :=
  (Submodule.span ℂ {f | ∃ n v, f = vectorMonomialL2 N n v}).topologicalClosure

/-- Nonempty proper open arcs are obtained from a < b < a+2π (§14, p.20).
The real endpoints are retained, so arcs crossing θ=0 are also allowed. -/
def angularArc (a b : ℝ) : Set AngularCircle :=
  (fun θ : ℝ => (θ : AngularCircle)) '' Set.Ioo a b

/-- Vanishing on an arc means Haar-a.e. vanishing of an L² representative (§14, p.20). -/
def VanishesOnArc {N : ℕ} (f : CircleL2 N) (a b : ℝ) : Prop :=
  ∀ᵐ θ ∂angularHaar, θ ∈ angularArc a b → f θ = 0

example (N n : ℕ) (v : EuclideanSpace ℂ (Fin N)) :
    vectorMonomialL2 N n v ∈ circleHardySpace N := by
  exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨n, v, rfl⟩)

example (N : ℕ) : (0 : CircleL2 N) ∈ circleHardySpace N :=
  (circleHardySpace N).zero_mem

example (a : ℝ) : angularArc a a = ∅ := by
  simp [angularArc]

/-- Rank-one operator Q(x)=φ(x)v (§18, PDF p.25).
This allows an arbitrary complex-linear functional φ; the frozen
Advance50.P38.rankOneMatrix instead denotes the Hermitian operator xx* and
cannot represent this source's general rank-one operator. -/
def linearRankOneMatrix {d : ℕ} (v : Fin d → ℂ)
    (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => v i * phi (Pi.single j 1)

/-- Resolvent scalar χ_A(t)=1+φ((tI−A)⁻¹v) (§22, PDF p.28).
Theorems evaluating it require the resolvent matrix to be invertible. -/
def resolventScalar {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) (t : ℂ) : ℂ :=
  1 + phi (((t • (1 : Matrix (Fin d) (Fin d) ℂ)) - A)⁻¹.mulVec v)

/-- The actual normalized spectral data of the basic ODE (§18, PDF p.25).
Both P and R=Q−P have simple nonresonant spectra and are in general position
with Q=vφ; mu records the eigenvalues of P−Q, not those of R. -/
structure BasicODEData (d : ℕ) where
  positiveDimension : 0 < d
  P : Matrix (Fin d) (Fin d) ℂ
  v : Fin d → ℂ
  phi : (Fin d → ℂ) →ₗ[ℂ] ℂ
  nonzeroTrace : phi v ≠ 0
  lambda : Fin d → ℂ
  mu : Fin d → ℂ
  xi : Module.Basis (Fin d) ℂ (Fin d → ℂ)
  zeta : Module.Basis (Fin d) ℂ (Fin d → ℂ)
  eigenP : ∀ i, P.mulVec (xi i) = lambda i • xi i
  eigenPminusQ : ∀ i, (P - linearRankOneMatrix v phi).mulVec (zeta i) = mu i • zeta i
  nonresonantLambda : ∀ i j, i ≠ j → ∀ n : ℤ, lambda i - lambda j ≠ (n : ℂ)
  nonresonantMu : ∀ i j, i ≠ j → ∀ n : ℤ, mu i - mu j ≠ (n : ℂ)
  normalizedXi : ∀ i, phi (xi i) = 1
  normalizedZeta : ∀ i, phi (zeta i) = 1
  generalPositionP : ∀ i, xi.repr v i ≠ 0
  generalPositionR : ∀ i, zeta.repr v i ≠ 0

example {d : ℕ} (phi : (Fin d → ℂ) →ₗ[ℂ] ℂ) :
    linearRankOneMatrix (0 : Fin d → ℂ) phi = 0 := by
  ext i j
  simp [linearRankOneMatrix]

/-- Recursive Frobenius coefficients and their partial sums (§22, PDF p.28).
The pair is (ξ_n, ξ_0+⋯+ξ_n), constructed from the ODE recurrence.
Nonresonance supplies every inverse at positive n in its applications. -/
def frobeniusPair {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ)
    (lambda : ℂ) (w : Fin d → ℂ) : ℕ → (Fin d → ℂ) × (Fin d → ℂ)
  | 0 => (w, w)
  | n + 1 =>
      let previous := frobeniusPair P Q lambda w n
      let next := (((lambda + ((n + 1 : ℕ) : ℂ)) •
        (1 : Matrix (Fin d) (Fin d) ℂ)) - P)⁻¹.mulVec (Q.mulVec previous.2)
      (next, previous.2 + next)

/-- α_{i,n}=φ(ξ_{i,0}+⋯+ξ_{i,n}) from the constructed Frobenius solution (§22, p.28). -/
def projectedCoefficient {d : ℕ} (A : BasicODEData d) (i : Fin d) (n : ℕ) : ℂ :=
  A.phi (frobeniusPair A.P (linearRankOneMatrix A.v A.phi) (A.lambda i) (A.xi i) n).2

example {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ) (lambda : ℂ) (w : Fin d → ℂ) :
    frobeniusPair P Q lambda w 0 = (w, w) := rfl

/-- Unnormalized integer signatures, before common-shift SU(N) equivalence (§2, p.8).
The frozen Dependency50.P26.Signature describes quantum-comb wire dimensions;
it is unrelated to these integer highest-weight coordinates. -/
abbrev IntegerSignature (N : ℕ) := Fin N → ℤ

/-- A signature is weakly decreasing (§2, PDF p.8). -/
def IsSignature {N : ℕ} (f : IntegerSignature N) : Prop :=
  ∀ i j, i ≤ j → f j ≤ f i

/-- Level-permissibility, expressed without artificial zero-padding (§§9,34, pp.16,43). -/
def IsPermissible {N : ℕ} (ell : ℕ) (f : IntegerSignature N) : Prop :=
  IsSignature f ∧ ∀ i j, f i - f j ≤ (ell : ℤ)

/-- Adding one actual box before renormalizing signatures (§2, p.8). -/
def AddsOneBox {N : ℕ} (f g : IntegerSignature N) : Prop :=
  ∃ row : Fin N, ∀ i, g i = f i + if i = row then 1 else 0

/-- A path retains every intermediate permissible signature (§32, pp.40–42). -/
structure BoxPath {N : ℕ} (ell k : ℕ) (f g : IntegerSignature N) where
  vertex : Fin (k + 1) → IntegerSignature N
  start : vertex 0 = f
  finish : vertex (Fin.last k) = g
  permissible : ∀ j, IsPermissible ell (vertex j)
  step : ∀ j : Fin k, AddsOneBox (vertex j.castSucc) (vertex j.succ)

/-- Adjacent paths differ at exactly one interior signature (§32, PDF pp.41–42). -/
def AdjacentPaths {N ell k : ℕ} {f g : IntegerSignature N}
    (P Q : BoxPath ell k f g) : Prop :=
  ∃ j : Fin (k + 1), 0 < j.val ∧ j.val < k ∧
    P.vertex j ≠ Q.vertex j ∧ ∀ i, i ≠ j → P.vertex i = Q.vertex i

example (N ell : ℕ) : IsPermissible ell (0 : IntegerSignature N) := by
  constructor
  · intro i j hij
    simp
  · intro i j
    simp

/-- An element of Λ₀⋊S_N, with translation (N+ℓ)m and Σm_i=0 (§34, PDF p.43). -/
structure AffineWeylElement (N : ℕ) where
  translation : Fin N → ℤ
  sumZero : ∑ i, translation i = 0
  permutation : Equiv.Perm (Fin N)

/-- Coordinate action with the usual inverse-permutation convention (§34, p.43). -/
def affineAction {N : ℕ} (ell : ℕ) (w : AffineWeylElement N)
    (x : Fin N → ℤ) : Fin N → ℤ :=
  fun i => x (w.permutation.symm i) + ((N + ell : ℕ) : ℤ) * w.translation i

/-- Trivial stabilizer in the actual affine action (§34, PDF p.43). -/
def HasTrivialStabilizer {N : ℕ} (ell : ℕ) (x : Fin N → ℤ) : Prop :=
  ∀ w : AffineWeylElement N, affineAction ell w x = x →
    w.translation = 0 ∧ w.permutation = Equiv.refl (Fin N)

/-- The source's Weyl shift δ=(N−1,…,0), with zero-based Lean indices (§34, p.43). -/
def weylShift (N : ℕ) : Fin N → ℤ := fun i => (N : ℤ) - 1 - (i.val : ℤ)

/-- Root-lattice membership uses zero-sum integral translations, not arbitrary shifts (§34, p.43). -/
def InAffineRootLattice {N : ℕ} (ell : ℕ) (x : Fin N → ℤ) : Prop :=
  ∃ m : Fin N → ℤ, (∑ i, m i) = 0 ∧
    ∀ i, x i = ((N + ell : ℕ) : ℤ) * m i

example : weylShift 2 = ![1, 0] := by
  ext i
  fin_cases i <;> norm_num [weylShift]

example (N ell : ℕ) : InAffineRootLattice (N := N) ell 0 := by
  refine ⟨0, by simp, ?_⟩
  intro i
  simp

/-- The nonresonant parameter set for a holomorphic family B=zA (§19, PDF p.26).
Zero eigenvalue differences are allowed; only positive integral differences are excluded. -/
def gaugeParameterSet {d m : ℕ}
    (B : (Fin m → ℂ) × ℂ → Matrix (Fin d) (Fin d) ℂ) : Set (Fin m → ℂ) :=
  {t | ∀ lambda mu : ℂ,
    (B (t, 0)).charpoly.eval lambda = 0 → (B (t, 0)).charpoly.eval mu = 0 →
    ∀ n : ℕ, 0 < n → lambda - mu ≠ (n : ℂ)}

/-- Holomorphic gauge domain including z=0 (§19, PDF p.26). -/
def gaugeDomain {d m : ℕ} (R : ℝ)
    (B : (Fin m → ℂ) × ℂ → Matrix (Fin d) (Fin d) ℂ) :
    Set ((Fin m → ℂ) × ℂ) :=
  gaugeParameterSet B ×ˢ Metric.ball 0 R

/-- A normalized holomorphic invertible matrix gauge; its equation is imposed
only for 0<|z|<R (§19, PDF p.26). Values outside the domain play no role. -/
def IsNormalizedGauge {d m : ℕ} (R : ℝ)
    (B g : (Fin m → ℂ) × ℂ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  DifferentiableOn ℂ g (gaugeDomain R B) ∧
  (∀ p ∈ gaugeDomain R B, (g p).det ≠ 0) ∧
  (∀ t ∈ gaugeParameterSet B, g (t, 0) = 1) ∧
  ∀ t ∈ gaugeParameterSet B, ∀ z : ℂ, ‖z‖ < R → z ≠ 0 →
    (g (t, z))⁻¹ * (z⁻¹ • B (t, z)) * g (t, z) -
      (g (t, z))⁻¹ * deriv (fun w : ℂ => g (t, w)) z = z⁻¹ • B (t, 0)

example {d m : ℕ} (B : (Fin m → ℂ) × ℂ → Matrix (Fin d) (Fin d) ℂ) :
    gaugeDomain 0 B = ∅ := by
  simp [gaugeDomain, Metric.ball_zero]

/-- Companion matrix with superdiagonal ones and last row a (§20, PDF pp.26–27). -/
def companionMatrix {d : ℕ} (a : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val + 1 = d then a j else if j.val = i.val + 1 then 1 else 0

/-- The simultaneous rank-one form has only its last row nonzero (§20, pp.26–27). -/
def lastRowMatrix {d : ℕ} (b : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val + 1 = d then b j else 0

/-- Polynomial a(t)=t^d−Σa_i t^(i−1), with zero-based Fin indices (§20, p.27). -/
def companionPolynomial {d : ℕ} (a : Fin d → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ d - ∑ i, Polynomial.C (a i) * Polynomial.X ^ i.val

/-- Polynomial b(t)=Σb_i t^(i−1) (§20, PDF p.27). -/
def rowPolynomial {d : ℕ} (b : Fin d → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.C (b i) * Polynomial.X ^ i.val

/-- No common complex root, not merely inequality of the two polynomials (§20, p.27). -/
def NoCommonRoot (a b : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ¬(a.eval z = 0 ∧ b.eval z = 0)

/-- Simple spectrum includes a full eigenbasis (§§18,20, PDF pp.25–27). -/
def HasSimpleSpectrum {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (e : Module.Basis (Fin d) ℂ (Fin d → ℂ)) (lambda : Fin d → ℂ),
    Function.Injective lambda ∧ ∀ i, P.mulVec (e i) = lambda i • e i

/-- Both-sided general position for a simple-spectrum P and rank-one Q:
Q annihilates no eigenline and its range has no zero eigenbasis coordinate (§20, p.26). -/
def RankOneGeneralPosition {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (e : Module.Basis (Fin d) ℂ (Fin d → ℂ)) (lambda : Fin d → ℂ),
    Function.Injective lambda ∧ (∀ i, P.mulVec (e i) = lambda i • e i) ∧
    (∀ i, Q.mulVec (e i) ≠ 0) ∧ ∀ i, ∃ x, e.repr (Q.mulVec x) i ≠ 0

example (a : Fin 1 → ℂ) : companionMatrix a 0 0 = a 0 := by
  simp [companionMatrix]

example (b : Fin 1 → ℂ) : lastRowMatrix b 0 0 = b 0 := by
  simp [lastRowMatrix]

/-- Real affine action, on all R^N rather than a zero-sum slice (§34, PDF p.43). -/
def realAffineAction {N : ℕ} (ell : ℕ) (w : AffineWeylElement N)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => x (w.permutation.symm i) + ((N + ell : ℕ) : ℝ) * (w.translation i : ℝ)

/-- Real zero-sum root-lattice translations (§34, PDF p.43). -/
def IsRealRootTranslation {N : ℕ} (ell : ℕ) (x : Fin N → ℝ) : Prop :=
  ∃ m : Fin N → ℤ, (∑ i, m i) = 0 ∧
    ∀ i, x i = ((N + ell : ℕ) : ℝ) * (m i : ℝ)

/-- Trivial stabilizer in the real affine action (§34, PDF p.43). -/
def HasTrivialRealStabilizer {N : ℕ} (ell : ℕ) (x : Fin N → ℝ) : Prop :=
  ∀ w : AffineWeylElement N, realAffineAction ell w x = x →
    w.translation = 0 ∧ w.permutation = Equiv.refl (Fin N)

/-- The symmetric closed translation domain (§34 lemma (a), PDF p.43). -/
def translationAlcove (N ell : ℕ) : Set (Fin N → ℝ) :=
  {x | ∀ i j, |x i - x j| ≤ ((N + ell : ℕ) : ℝ)}

/-- The closed dominant affine alcove (§34 lemma (b), PDF p.43). -/
def dominantAlcove (N ell : ℕ) : Set (Fin N → ℝ) :=
  {x | (∀ i j, i ≤ j → x j ≤ x i) ∧
    ∀ i j, x i - x j ≤ ((N + ell : ℕ) : ℝ)}

/-- Closed fundamental domain: orbit coverage and no overlap of interiors under
nonidentity translations. Boundary duplicates are allowed (§34, PDF p.43). -/
def IsTranslationFundamentalDomain {N : ℕ} (ell : ℕ) (D : Set (Fin N → ℝ)) : Prop :=
  IsClosed D ∧
  (∀ x : Fin N → ℝ, ∃ a : Fin N → ℝ, IsRealRootTranslation ell a ∧ x + a ∈ D) ∧
  ∀ x a : Fin N → ℝ, IsRealRootTranslation ell a →
    x ∈ interior D → x + a ∈ interior D → a = 0

/-- Closed fundamental domain for the affine Weyl action (§34, PDF p.43). -/
def IsAffineFundamentalDomain {N : ℕ} (ell : ℕ) (D : Set (Fin N → ℝ)) : Prop :=
  IsClosed D ∧
  (∀ x : Fin N → ℝ, ∃ w : AffineWeylElement N, realAffineAction ell w x ∈ D) ∧
  ∀ (w : AffineWeylElement N) (x : Fin N → ℝ),
    x ∈ interior D → realAffineAction ell w x ∈ interior D →
      w.translation = 0 ∧ w.permutation = Equiv.refl (Fin N)

example (N ell : ℕ) : (0 : Fin N → ℝ) ∈ dominantAlcove N ell := by
  constructor
  · intro i j hij
    simp
  · intro i j
    simpa using (Nat.cast_nonneg (N + ell) : (0 : ℝ) ≤ ((N + ell : ℕ) : ℝ))

section StandardRealPart

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

/-- Cyclicity uses the norm-dense actual operator orbit MΩ (§12, PDF p.18). -/
def IsCyclicFor (M : VonNeumannAlgebra H) (omega : H) : Prop :=
  Dense {x : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ x = a omega}

/-- K is the real closed span of self-adjoint vectors aΩ (§12, PDF p.18).
This does not assume standardness or any modular identities. -/
def closedSelfAdjointRealPart (M : VonNeumannAlgebra H) (omega : H) : Submodule ℝ H :=
  (Submodule.span ℝ {x : H | ∃ a : H →L[ℂ] H,
    a ∈ M ∧ IsSelfAdjoint a ∧ x = a omega}).topologicalClosure

/-- The real subspace iK uses the original complex structure (§12, PDF p.18). -/
def imaginaryRealPart (K : Submodule ℝ H) : Submodule ℝ H :=
  K.map ((Complex.I • (LinearMap.id : H →ₗ[ℂ] H)).restrictScalars ℝ)

example : imaginaryRealPart (⊥ : Submodule ℝ H) = ⊥ := by
  simp [imaginaryRealPart]

end StandardRealPart

end QAlgorithms.Papers.Independent.Intakenext100.P41


