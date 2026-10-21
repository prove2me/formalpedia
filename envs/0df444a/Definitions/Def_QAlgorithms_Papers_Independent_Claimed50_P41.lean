-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
-- name    : QAlgorithms_Papers_Independent_Claimed50_P41
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:54:03.913036+00:00
-- url     : https://prove2.me/theorems/4dc913ee-f6ee-404b-af97-85fb4f2d37de
-- title:
--   Definitions for The Real Symplectic Groups in Quantum Mechanics and Optics
-- statement:
--   The objects the formalized statements of *The Real Symplectic Groups in Quantum Mechanics and Optics* (arXiv:quant-ph/9509002) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PreservesCanonicalForm`: Symplecticity, PDF p.6 (2.5).
--   - `linearCanonicalBracket`: PB coefficient, equivalently the quantum commutator divided by i hbar, of transformed linear coordinates, PDF pp.5–6 (2.3)–(2.5).
--   - `Schrodinger`: Cartesian Schrodinger space with product Lebesgue measure, PDF p.6 (2.7).
--   - `displacedFunction`: Concrete D(d,p)f(q)=exp(i p.(q-d/2))f(q-d), PDF pp.26–28 (7.4),(8.3).
--   - `IsImplementer`: Concrete Weyl meaning of U^{-1}xi U=S xi, PDF p.6 (2.8). The existential vector realizes D(z)psi in L2, preventing a vacuous conditional. The equality is U D(z)=D(Sz) U; no unbounded operator is treated as bounded.
--   - `symplecticRank`: Rank of the restricted form W -> W*, PDF p.8 (3.6).
--   - `IsIsotropic`: Isotropic, PDF p.10 (3.14).
--   - `IsCoisotropic`: Co-isotropic, PDF p.10 (3.15).
--   - `IsLagrangian`: Lagrangian, PDF p.10.
--   - `IsPassive`: Passive K(n), PDF pp.13–14 (4.11).
--   - `IsPositiveSymplectic`: Pi(n), a positive symplectic subset, PDF p.15 (4.18).
--   - `passiveMatrix`: Realification S(X,Y), PDF p.13 (4.10).
--   - `unitaryParameter`: U=X-iY, PDF p.13 (4.9).
--   - `glMatrix`: GL embedding, PDF p.13 (4.7); invertibility guarded in the theorem.
--   - `freeMatrix`: Free propagation, PDF p.14 (4.15).
--   - `lensMatrix`: Lens with plus C, PDF p.15 (4.17); L(g) in (6.6c) uses C=-g.
--   - `squeezeMatrix`: Positive diagonal squeeze, PDF p.16 (4.20).
--   - `IsMatrixSubgroup`: Matrix subgroup as a subset; symplectic membership is separately required. Used for inclusion-maximal compactness, PDF pp.13–14.
--   - `canonicalCoordinateMatrix`: Omega, the complex coordinate change, PDF p.12 (4.4).
--   - `sigma3`: Sigma3, PDF p.12 (4.5).
--   - `complexForm`: S^(c), PDF p.12 (4.6), also V^(c) for symmetric V in (8.6).
--   - `positiveSqrt`: Spectral positive square root on positive definite inputs, PDF pp.16,35. Off the self-adjoint domain generic CFC is totalized; all uses carry guards.
--   - `preA`: Constructed A0, PDF p.16 (4.21).
--   - `preC`: Constructed C0, PDF p.16 (4.21).
--   - `IsNilpotentFactor`: N factor: lower unitriangular A, matching the displayed zeros in (4.23), PDF pp.17–18.
--   - `noiseA`: Complex variance block A, PDF p.29 (8.6).
--   - `noiseB`: Complex variance block B, PDF p.29 (8.6).
--   - `Allowed`: Matrix family S, PDF p.33 (11.1), vacuum I/2. This does not define a state as a covariance tuple; density-operator realizability is separately deferred.
--   - `IsDiagonal`: Diagonalness, PDF p.31 (9.4).
--   - `IsRealDiagonal`: Real diagonal complex matrix, PDF p.31 (9.4).
--   - `ManifestSqueezing`: Manifest variance squeezing, PDF p.32 (10.5).
--   - `PassiveSqueezing`: Passive-invariant squeezing, PDF p.32 (10.5).
--   - `minimumEigenvalue`: Finite minimum of ordinary real eigenvalues, PDF p.33 (10.6). Hermiticity and n>0 are required, so the minimum has no junk default.
--   - `familyK`: Family SK, PDF p.34 (11.2).
--   - `familyH`: Family SH, PDF p.34 (11.4).
--   - `familyG`: Family SG, PDF p.34 (11.5).
--   - `gaussianWave`: Gaussian representative with positive normalization, PDF p.35 (12.1).
--   - `IsCenteredGaussianFunction`: General centred Gaussian function means a nonzero constant times a quadratic exponential with positive real precision, PDF p.35 (12.1). Normalization and its scalar phase are conclusions of the theorem below.
--   - `quadratureFunction`: Concrete multiplication/differentiation actions, PDF p.6 (2.7), only used on smooth Gaussian functions, not unrestricted L2 representatives.
--   - `waveMean`: First moment on the integrable Gaussian domain, PDF p.27 (8.1).
--   - `waveCovariance`: Central symmetrized quadrature form on the integrable Gaussian domain, PDF p.28 (8.2), applied in p.35 (12.3).
--   - `gaussianPrecision`: Precision G(u,v), PDF p.35 (12.3).
--   - `gaussianSymplectic`: Constructed S(u,v), PDF p.35 (12.3).
--   - `waveWigner`: Pure-state Wigner integral, PDF p.35 (12.3); the theorem supplies integrability.
--   - `gaussianCoordinate`: Lambda=(iu-v)^{-1}, PDF p.37 (12.7); denominator invertibility is a conclusion.
--   - `realGenerator`: The real matrix -i X^(0)_ab, PDF p.19 (5.2).
--   - `generatorMatrix`: The source's imaginary generator X^(0)_ab=i times the real generator, PDF p.19 (5.2); retaining this i is essential to its commutator signs.
--   - `phaseNumber`: Grouped coordinate number, used to choose a<=b exactly once in (5.2).
--   - `algebraCommutator`: Algebra commutator, Section V.
--   - `GeneratorRepresentation`: Representation of the generator presentation (5.4), PDF p.19. This is a representation of the complexified symplectic Lie algebra by its symmetric generators and all defining brackets, not unrelated arbitrary operators. No boundedness or Hilbert-space adjoint is built into a generic representation.
--   - `splitV`: Split V generator, PDF p.19 (5.6).
--   - `splitW`: Split W generator, PDF p.19 (5.6).
--   - `splitZ`: Split Z generator, PDF p.19 (5.6).
--   - `compactJ`: Compact J=W_sr-W_rs, PDF p.20 table.
--   - `compactQ`: Compact Q=V+Z, PDF p.20 table.
--   - `adaptedA`: U(n)-adapted A=(Q-iJ)/2, PDF p.20 table.
--   - `tensorLower`: T_lower=V-Z-i(W+W^T), PDF p.21 (5.9).
--   - `tensorUpper`: T_upper=V-Z+i(W+W^T), PDF p.21 (5.9).
--   - `kronecker`: Kronecker delta as a complex scalar, PDF p.21 (5.10).
--   - `annihilationFunction`: Annihilation as the actual differential expression (q+ip)/sqrt(2), PDF p.12 (4.3). Core identities quantify over Schwartz functions.
--   - `creationFunction`: Creation as the actual differential expression (q-ip)/sqrt(2), PDF p.12 (4.3). This is not a bounded endomorphism of L2.
--   - `coherentDisplacement`: Complex coherent label converted to real displacement (sqrt(2) Re z, sqrt(2) Im z), PDF pp.25–26 (7.3)–(7.4), hbar=1.
--   - `coherentWave`: Canonical coherent wavefunction D(z)|0>, PDF pp.25–26 (7.3)–(7.4), with its Weyl half-phase retained.
--   - `multimodeCoherentMeasure`: Coherent frame measure product d^2 z_r/pi, PDF p.26 (7.5).
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, https://arxiv.org/abs/quant-ph/9509002v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
Arvind–Dutta–Mukunda–Simon, arXiv:quant-ph/9509002v3. Grouped q,p order,
hbar=1, vacuum covariance I/2. P10 supplies the exact grouped index, beta,
complexification and Williamson diagonal; its physicalCovariance is not used.
Concrete operator assertions use L2(R^n), with almost-everywhere equality.
Deferrals are listed individually in HARD.md/GAPS.json. Compilation pending.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- Symplecticity, PDF p.6 (2.5). -/
def PreservesCanonicalForm {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  S * sigma n * S.transpose = sigma n

/-- PB coefficient, equivalently the quantum commutator divided by i hbar,
of transformed linear coordinates, PDF pp.5–6 (2.3)–(2.5). -/
def linearCanonicalBracket {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ)
    (a b : Phase n) : ℝ := ∑ i, ∑ j, S a i * sigma n i j * S b j

/-- Cartesian Schrodinger space with product Lebesgue measure, PDF p.6 (2.7). -/
abbrev Schrodinger (n : ℕ) := Lp ℂ 2 (volume : Measure (Fin n → ℝ))

/-- Concrete D(d,p)f(q)=exp(i p.(q-d/2))f(q-d), PDF pp.26–28 (7.4),(8.3). -/
def displacedFunction {n : ℕ} (z : Phase n → ℝ)
    (f : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ i, z (Sum.inr i) *
    (q i - z (Sum.inl i) / 2) : ℝ) : ℂ)) * f (fun i => q i - z (Sum.inl i))

/-- Concrete Weyl meaning of U^{-1}xi U=S xi, PDF p.6 (2.8).
The existential vector realizes D(z)psi in L2, preventing a vacuous conditional.
The equality is U D(z)=D(Sz) U; no unbounded operator is treated as bounded. -/
def IsImplementer {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ)
    (U : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n) : Prop :=
  ∀ (z : Phase n → ℝ) (psi : Schrodinger n), ∃ phi : Schrodinger n,
    (fun q => phi q) =ᵐ[volume] displacedFunction z (fun q => psi q) ∧
    (fun q => U phi q) =ᵐ[volume] displacedFunction (Matrix.mulVec (S) z) (fun q => U psi q)

/-- Rank of the restricted form W -> W*, PDF p.8 (3.6). -/
def symplecticRank {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (W : Submodule ℝ V) : ℕ :=
  Module.finrank ℝ (LinearMap.range (B.restrict W))

/-- Isotropic, PDF p.10 (3.14). -/
def IsIsotropic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (W : Submodule ℝ V) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, B x y = 0

/-- Co-isotropic, PDF p.10 (3.15). -/
def IsCoisotropic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (W : Submodule ℝ V) : Prop := IsIsotropic B (B.orthogonal W)

/-- Lagrangian, PDF p.10. -/
def IsLagrangian {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (W : Submodule ℝ V) : Prop := W = B.orthogonal W

/-- Passive K(n), PDF pp.13–14 (4.11). -/
def IsPassive {n : ℕ} (K : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  PreservesCanonicalForm K ∧ K.transpose * K = 1

/-- Pi(n), a positive symplectic subset, PDF p.15 (4.18). -/
def IsPositiveSymplectic {n : ℕ} (P : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  PreservesCanonicalForm P ∧ P.PosDef

/-- Realification S(X,Y), PDF p.13 (4.10). -/
def passiveMatrix {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ := Matrix.fromBlocks X Y (-Y) X

/-- U=X-iY, PDF p.13 (4.9). -/
def unitaryParameter {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ := complexify X - Complex.I • complexify Y

/-- GL embedding, PDF p.13 (4.7); invertibility guarded in the theorem. -/
def glMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ := Matrix.fromBlocks A 0 0 A⁻¹.transpose

/-- Free propagation, PDF p.14 (4.15). -/
def freeMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ := Matrix.fromBlocks 1 B 0 1

/-- Lens with plus C, PDF p.15 (4.17); L(g) in (6.6c) uses C=-g. -/
def lensMatrix {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ := Matrix.fromBlocks 1 0 C 1

/-- Positive diagonal squeeze, PDF p.16 (4.20). -/
def squeezeMatrix {n : ℕ} (kappa : Fin n → ℝ) : Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal kappa) 0 0 (Matrix.diagonal (fun i => (kappa i)⁻¹))

/-- Matrix subgroup as a subset; symplectic membership is separately required.
Used for inclusion-maximal compactness, PDF pp.13–14. -/
def IsMatrixSubgroup {n : ℕ} (H : Set (Matrix (Phase n) (Phase n) ℝ)) : Prop :=
  (1 : Matrix (Phase n) (Phase n) ℝ) ∈ H ∧
  (∀ A ∈ H, ∀ B ∈ H, A * B ∈ H) ∧ (∀ A ∈ H, A⁻¹ ∈ H)

/-- Omega, the complex coordinate change, PDF p.12 (4.4). -/
def canonicalCoordinateMatrix (n : ℕ) : Matrix (Phase n) (Phase n) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • Matrix.fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1)

/-- Sigma3, PDF p.12 (4.5). -/
def sigma3 (n : ℕ) : Matrix (Phase n) (Phase n) ℂ := Matrix.fromBlocks 1 0 0 (-1)

/-- S^(c), PDF p.12 (4.6), also V^(c) for symmetric V in (8.6). -/
def complexForm {n : ℕ} (S : Matrix (Phase n) (Phase n) ℝ) :
    Matrix (Phase n) (Phase n) ℂ := canonicalCoordinateMatrix n * complexify S * (canonicalCoordinateMatrix n).conjTranspose

/-- Spectral positive square root on positive definite inputs, PDF pp.16,35.
Off the self-adjoint domain generic CFC is totalized; all uses carry guards. -/
def positiveSqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  cfc Real.sqrt A

/-- Constructed A0, PDF p.16 (4.21). -/
def preA {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) := positiveSqrt (A * A.transpose + B * B.transpose)

/-- Constructed C0, PDF p.16 (4.21). -/
def preC {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℝ) :=
  (C * A.transpose + D * B.transpose) * (preA A B)⁻¹

/-- N factor: lower unitriangular A, matching the displayed zeros in (4.23),
PDF pp.17–18. -/
def IsNilpotentFactor {n : ℕ} (N : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  ∃ A C : Matrix (Fin n) (Fin n) ℝ,
    (∀ i, A i i = 1) ∧ (∀ i j, i < j → A i j = 0) ∧
    (A.transpose * C).IsSymm ∧ N = Matrix.fromBlocks A 0 C A⁻¹.transpose

/-- Complex variance block A, PDF p.29 (8.6). -/
def noiseA {n : ℕ} (V : Matrix (Phase n) (Phase n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (complexForm V).submatrix Sum.inl Sum.inl

/-- Complex variance block B, PDF p.29 (8.6). -/
def noiseB {n : ℕ} (V : Matrix (Phase n) (Phase n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (complexForm V).submatrix Sum.inl Sum.inr

/-- Matrix family S, PDF p.33 (11.1), vacuum I/2. This does not define a
state as a covariance tuple; density-operator realizability is separately deferred. -/
def Allowed {n : ℕ} (V : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  V.PosDef ∧ (complexify V + (Complex.I / 2) • complexify (sigma n)).PosSemidef

/-- Diagonalness, PDF p.31 (9.4). -/
def IsDiagonal {I K : Type*} [Zero K] (M : Matrix I I K) : Prop := ∀ i j, i ≠ j → M i j = 0

/-- Real diagonal complex matrix, PDF p.31 (9.4). -/
def IsRealDiagonal {I : Type*} (M : Matrix I I ℂ) : Prop :=
  IsDiagonal M ∧ ∀ i j, (M i j).im = 0

/-- Manifest variance squeezing, PDF p.32 (10.5). -/
def ManifestSqueezing {n : ℕ} (V : Matrix (Phase n) (Phase n) ℝ) : Prop := ∃ a, V a a < 1 / 2

/-- Passive-invariant squeezing, PDF p.32 (10.5). -/
def PassiveSqueezing {n : ℕ} (V : Matrix (Phase n) (Phase n) ℝ) : Prop :=
  ∃ K : Matrix (Phase n) (Phase n) ℝ, IsPassive K ∧ ManifestSqueezing (K * V * K.transpose)

/-- Finite minimum of ordinary real eigenvalues, PDF p.33 (10.6).
Hermiticity and n>0 are required, so the minimum has no junk default. -/
def minimumEigenvalue {n : ℕ} (hn : 0 < n) (V : Matrix (Phase n) (Phase n) ℝ)
    (hV : V.IsHermitian) : ℝ :=
  Finset.univ.inf' (show (Finset.univ : Finset (Phase n)).Nonempty from
    ⟨Sum.inl ⟨0, hn⟩, Finset.mem_univ _⟩) hV.eigenvalues

/-- Family SK, PDF p.34 (11.2). -/
def familyK (n : ℕ) : Set (Matrix (Phase n) (Phase n) ℝ) :=
  {V | Allowed V ∧ (noiseA V * noiseB V).IsSymm}

/-- Family SH, PDF p.34 (11.4). -/
def familyH (n : ℕ) : Set (Matrix (Phase n) (Phase n) ℝ) :=
  {V | V ∈ familyK n ∧ noiseB V = 0 ∧
    (noiseA V - (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef}

/-- Family SG, PDF p.34 (11.5). -/
def familyG (n : ℕ) : Set (Matrix (Phase n) (Phase n) ℝ) :=
  {V | V ∈ familyK n ∧ IsPositiveSymplectic ((2 : ℝ) • V)}

/-- Gaussian representative with positive normalization, PDF p.35 (12.1). -/
def gaussianWave {n : ℕ} (u v : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) : ℂ :=
  (Real.rpow Real.pi (-(n : ℝ) / 4) * Real.rpow u.det (1 / 4) : ℝ) *
    Complex.exp (-(1 / 2 : ℂ) *
      ∑ i, ∑ j, (q i : ℂ) * ((u i j : ℂ) + Complex.I * (v i j : ℂ)) * (q j : ℂ))

/-- General centred Gaussian function means a nonzero constant times a
quadratic exponential with positive real precision, PDF p.35 (12.1).
Normalization and its scalar phase are conclusions of the theorem below. -/
def IsCenteredGaussianFunction {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  ∃ u v : Matrix (Fin n) (Fin n) ℝ, ∃ c : ℂ,
    u.PosDef ∧ v.IsSymm ∧ c ≠ 0 ∧ ∀ q,
      f q = c * Complex.exp (-(1 / 2 : ℂ) *
        ∑ i, ∑ j, (q i : ℂ) * ((u i j : ℂ) + Complex.I * (v i j : ℂ)) * (q j : ℂ))

/-- Concrete multiplication/differentiation actions, PDF p.6 (2.7),
only used on smooth Gaussian functions, not unrestricted L2 representatives. -/
def quadratureFunction {n : ℕ} (a : Phase n) (f : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) : ℂ :=
  match a with
  | Sum.inl i => (q i : ℂ) * f q
  | Sum.inr i => -Complex.I * (fderiv ℝ f q) (Pi.single i 1)

/-- First moment on the integrable Gaussian domain, PDF p.27 (8.1). -/
def waveMean {n : ℕ} (f : (Fin n → ℝ) → ℂ) (a : Phase n) : ℝ :=
  ∫ q, (star (f q) * quadratureFunction a f q).re

/-- Central symmetrized quadrature form on the integrable Gaussian domain,
PDF p.28 (8.2), applied in p.35 (12.3). -/
def waveCovariance {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Matrix (Phase n) (Phase n) ℝ :=
  fun a b => (∫ q, (star (quadratureFunction a f q) * quadratureFunction b f q).re) -
    waveMean f a * waveMean f b

/-- Precision G(u,v), PDF p.35 (12.3). -/
def gaussianPrecision {n : ℕ} (u v : Matrix (Fin n) (Fin n) ℝ) : Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks (u + v * u⁻¹ * v) (v * u⁻¹) (u⁻¹ * v) u⁻¹

/-- Constructed S(u,v), PDF p.35 (12.3). -/
def gaussianSymplectic {n : ℕ} (u v : Matrix (Fin n) (Fin n) ℝ) : Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks (positiveSqrt u)⁻¹ 0 (-v * (positiveSqrt u)⁻¹) (positiveSqrt u)

/-- Pure-state Wigner integral, PDF p.35 (12.3); the theorem supplies integrability. -/
def waveWigner {n : ℕ} (f : (Fin n → ℝ) → ℂ) (z : Phase n → ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) ^ n : ℂ)⁻¹ * ∫ y : Fin n → ℝ,
    f (fun i => z (Sum.inl i) - y i / 2) * star (f (fun i => z (Sum.inl i) + y i / 2)) *
      Complex.exp (Complex.I * ((∑ i, y i * z (Sum.inr i) : ℝ) : ℂ))

/-- Lambda=(iu-v)^{-1}, PDF p.37 (12.7); denominator invertibility is a conclusion. -/
def gaussianCoordinate {n : ℕ} (u v : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (Complex.I • complexify u - complexify v)⁻¹

example : sigma 1 (Sum.inl 0) (Sum.inr 0) = 1 := by
  norm_num [sigma, Matrix.fromBlocks]

example : sigma 1 (Sum.inr 0) (Sum.inl 0) = -1 := by
  norm_num [sigma, Matrix.fromBlocks]

example {n : ℕ} (f : (Fin n → ℝ) → ℂ) : displacedFunction 0 f = f := by
  funext q
  simp [displacedFunction]

example {n : ℕ} : freeMatrix (0 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [freeMatrix, Matrix.fromBlocks, Matrix.one_apply]

example {n : ℕ} : lensMatrix (0 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [lensMatrix, Matrix.fromBlocks, Matrix.one_apply]

example {n : ℕ} : squeezeMatrix (fun _ : Fin n => (1 : ℝ)) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [squeezeMatrix, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]

example {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) : IsIsotropic B ⊥ := by
  intro x hx y hy
  have hx0 : x = 0 := by simpa using hx
  simp [hx0]

/-- The real matrix -i X^(0)_ab, PDF p.19 (5.2). -/
def realGenerator {n : ℕ} (a b : Phase n) : Matrix (Phase n) (Phase n) ℝ :=
  fun c d => (if a = d then sigma n c b else 0) + (if b = d then sigma n c a else 0)

/-- The source's imaginary generator X^(0)_ab=i times the real generator,
PDF p.19 (5.2); retaining this i is essential to its commutator signs. -/
def generatorMatrix {n : ℕ} (a b : Phase n) : Matrix (Phase n) (Phase n) ℂ :=
  Complex.I • complexify (realGenerator a b)

/-- Grouped coordinate number, used to choose a<=b exactly once in (5.2). -/
def phaseNumber {n : ℕ} : Phase n → ℕ
  | Sum.inl i => i.val
  | Sum.inr i => n + i.val

/-- Algebra commutator, Section V. -/
def algebraCommutator {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X

/-- Representation of the generator presentation (5.4), PDF p.19.
This is a representation of the complexified symplectic Lie algebra by its
symmetric generators and all defining brackets, not unrelated arbitrary operators.
No boundedness or Hilbert-space adjoint is built into a generic representation. -/
structure GeneratorRepresentation (n : ℕ) (R : Type*) [Ring R] [Algebra ℂ R] where
  X : Phase n → Phase n → R
  symmetric : ∀ a b, X a b = X b a
  bracket : ∀ a b c d, algebraCommutator (X a b) (X c d) = Complex.I •
    ((sigma n a c : ℂ) • X b d + (sigma n b c : ℂ) • X a d +
      (sigma n a d : ℂ) • X c b + (sigma n b d : ℂ) • X c a)

/-- Split V generator, PDF p.19 (5.6). -/
def splitV {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) := rho.X (Sum.inl r) (Sum.inl s)

/-- Split W generator, PDF p.19 (5.6). -/
def splitW {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) := rho.X (Sum.inl r) (Sum.inr s)

/-- Split Z generator, PDF p.19 (5.6). -/
def splitZ {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) := rho.X (Sum.inr r) (Sum.inr s)

/-- Compact J=W_sr-W_rs, PDF p.20 table. -/
def compactJ {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) := splitW rho s r - splitW rho r s

/-- Compact Q=V+Z, PDF p.20 table. -/
def compactQ {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) := splitV rho r s + splitZ rho r s

/-- U(n)-adapted A=(Q-iJ)/2, PDF p.20 table. -/
def adaptedA {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) :=
  (1 / 2 : ℂ) • (compactQ rho r s - Complex.I • compactJ rho r s)

/-- T_lower=V-Z-i(W+W^T), PDF p.21 (5.9). -/
def tensorLower {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) :=
  splitV rho r s - splitZ rho r s - Complex.I • (splitW rho r s + splitW rho s r)

/-- T_upper=V-Z+i(W+W^T), PDF p.21 (5.9). -/
def tensorUpper {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) :=
  splitV rho r s - splitZ rho r s + Complex.I • (splitW rho r s + splitW rho s r)

/-- Kronecker delta as a complex scalar, PDF p.21 (5.10). -/
def kronecker {n : ℕ} (i j : Fin n) : ℂ := if i = j then 1 else 0

example : generatorMatrix (Sum.inl (0 : Fin 1)) (Sum.inl 0)
    (Sum.inr 0) (Sum.inl 0) = -2 * Complex.I := by
  norm_num [generatorMatrix, realGenerator, complexify, sigma, Matrix.fromBlocks, mul_comm]

example {n : ℕ} {R : Type*} [Ring R] [Algebra ℂ R]
    (rho : GeneratorRepresentation n R) (r s : Fin n) : splitV rho r s = splitV rho s r :=
  rho.symmetric _ _

/-- Annihilation as the actual differential expression (q+ip)/sqrt(2),
PDF p.12 (4.3). Core identities quantify over Schwartz functions. -/
def annihilationFunction {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) : ℂ :=
  (quadratureFunction (Sum.inl i) f q + Complex.I * quadratureFunction (Sum.inr i) f q) /
    (Real.sqrt 2 : ℂ)

/-- Creation as the actual differential expression (q-ip)/sqrt(2),
PDF p.12 (4.3). This is not a bounded endomorphism of L2. -/
def creationFunction {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℂ) (q : Fin n → ℝ) : ℂ :=
  (quadratureFunction (Sum.inl i) f q - Complex.I * quadratureFunction (Sum.inr i) f q) /
    (Real.sqrt 2 : ℂ)

/-- Complex coherent label converted to real displacement (sqrt(2) Re z,
sqrt(2) Im z), PDF pp.25–26 (7.3)–(7.4), hbar=1. -/
def coherentDisplacement {n : ℕ} (z : Fin n → ℂ) : Phase n → ℝ
  | Sum.inl i => Real.sqrt 2 * (z i).re
  | Sum.inr i => Real.sqrt 2 * (z i).im

/-- Canonical coherent wavefunction D(z)|0>, PDF pp.25–26 (7.3)–(7.4),
with its Weyl half-phase retained. -/
def coherentWave {n : ℕ} (z : Fin n → ℂ) : (Fin n → ℝ) → ℂ :=
  displacedFunction (coherentDisplacement z) (gaussianWave (1 : Matrix (Fin n) (Fin n) ℝ) 0)

/-- Coherent frame measure product d^2 z_r/pi, PDF p.26 (7.5). -/
def multimodeCoherentMeasure (n : ℕ) : Measure (Fin n → ℂ) :=
  (ENNReal.ofReal ((Real.pi ^ n)⁻¹)) • volume

example {n : ℕ} : coherentDisplacement (0 : Fin n → ℂ) = 0 := by
  funext i
  cases i <;> simp [coherentDisplacement]

end QAlgorithms.Papers.Independent.Claimed50.P41


