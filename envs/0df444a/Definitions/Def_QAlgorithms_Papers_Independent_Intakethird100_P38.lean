-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P38
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:22:09.100821+00:00
-- url     : https://prove2.me/theorems/7dbf2b7c-03a1-48e3-a17e-1a2570a91108
-- title:
--   Definitions for Stochastic processes induced by singular operators
-- statement:
--   The objects the formalized statements of *Stochastic processes induced by singular operators* (arXiv:1109.5273) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SpectralDomain`: Euclidean R^n with its Euclidean norm and ordinary Lebesgue volume.
--   - `ComplexTest`: Complex Schwartz functions, with Mathlib's full Schwartz Fréchet topology.
--   - `RealTest`: Real Schwartz functions, with their Schwartz Fréchet topology.
--   - `Omega`: The continuous REAL tempered dual, not the algebraic dual.
--   - `paperFourier`: The unnormalized Fourier integral of (1.2), p.3.
--   - `decayWeight`: The positive weight in (1.1), including p=0.
--   - `weightedMass`: Extended weighted mass: divergence is infinity, never Bochner's default zero.
--   - `InC`: The regular positive Borel spectral measures C of (1.1) and Definition 3.1.
--   - `fourierEnergy`: The spectral quadratic integral, defined before any finiteness assertion.
--   - `spectralQ`: The real-valued quadratic form; used with explicit finiteness or InC.
--   - `realFunction`: Include a real test function in the complex-valued functions.
--   - `spectralPairing`: The source's covariance, linear in ψ and conjugate-linear in φ.
--   - `PositiveQuadratic`: All three axioms (3.1)--(3.3), not nonnegativity alone.
--   - `testTranslation`: U_t ψ(x)=ψ(x-t), equation (3.4).
--   - `L2`: Actual complex L2 classes for a measure, including the zero measure.
--   - `l2Class`: Total L2 packaging. Every use on a paper test is justified by InC or a conclusion asserting MemLp; the fallback is never used as an integrability test.
--   - `fourierClass`: Fourier inclusion into the spectral L2 space.
--   - `factorFromW`: Equation (3.7) after cancellation of its two reciprocal weights.
--   - `HilbertFactor`: Equation (3.6), with Mathlib's inner-product slots reversed to match the source.
--   - `spectralCompletion`: A concrete model of the separated spectral completion: close the Fourier image in L2(σ). Taking the span is harmless because that image is linear on InC.
--   - `spectralVector`: The canonical image of a test in its separated spectral completion.
--   - `LocallyTotalExponentials`: Local totality means density of the COMPLEX LINEAR SPAN of exponentials.
--   - `Closable`: Definition 4.1, with the ambient norm from L2(dx) and two independent tail indices.
--   - `CharacteristicLaw`: A law is specified by its real characteristic functional, not complex mixed covariances. The finite-energy clause makes conversion to real numbers explicit.
--   - `AntiDual`: Continuous anti-duals express the source's distribution paired against a conjugated test. This keeps the first-slot linear source convention explicit.
--   - `spectralDistribution`: The distribution specified by the spectral pairing itself. Its representing continuous functional exists on InC; that assertion remains a theorem conclusion.
--   - `adjointProduct`: The actual distributional adjoint product, computed from Q, without a kernel hypothesis.
--   - `covarianceKernel`: The covariance kernel of §6 as scalar multiplication operators, for RKHS.OfKernel.
--   - `lawFourier`: Formula (6.1), on the full complex L2 probability space.
--   - `distributionShift`: θ_t ω=ω(·-t) as a distribution: θ_t ω(ψ)=ω(ψ(·+t)).
--   - `KoopmanFamily`: Full complex L2 unitaries, including the constants.
--   - `IsKoopman`: Measure preservation, group law, and actual pullback on ae classes.
--   - `ShiftErgodic`: Ergodicity for the whole translation group, using measurable sets invariant modulo null sets.
--   - `TrivialPointSpectrum`: No nonzero joint frequency, AND the zero eigenspace consists exactly of constants. For a probability law the constants form a one-dimensional complex space.
--   - `InCb`: Definition (11.1): q and C are chosen before the arbitrary translation v.
--   - `measureConvolution`: Extended-valued convolution; the output is not assumed locally finite.
--   - `point1`: Identify R with one-dimensional Euclidean space without changing Lebesgue normalization.
--   - `diracComb`: The integer Dirac comb, as a genuine measure.
--   - `SequenceL2`: ℓ²(Z), modeled as L2 of counting measure.
--   - `combSamples`: Integer Fourier samples; square summability remains part of Proposition 12.1.
--   - `periodization`: The periodization sum from (12.2); the adjoint product has an extra factor 2π.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, https://arxiv.org/abs/1109.5273v1

import Mathlib

/-!
Statements from Alpay--Jorgensen, arXiv:1109.5273v1.
All paper-specific definitions are local. Fourier transforms use exp(-i u.x),
ordinary Lebesgue measure, and no normalization factor. Source corrections and
source-ambiguous deferrals are recorded in the unit's moderation notes and HARD.md.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter
open scoped Topology ComplexConjugate ENNReal

/-- Euclidean R^n with its Euclidean norm and ordinary Lebesgue volume. -/
abbrev SpectralDomain (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Complex Schwartz functions, with Mathlib's full Schwartz Fréchet topology. -/
abbrev ComplexTest (n : ℕ) := SchwartzMap (SpectralDomain n) ℂ

/-- Real Schwartz functions, with their Schwartz Fréchet topology. -/
abbrev RealTest (n : ℕ) := SchwartzMap (SpectralDomain n) ℝ

/-- The continuous REAL tempered dual, not the algebraic dual. -/
abbrev Omega (n : ℕ) := RealTest n →L[ℝ] ℝ

/-- The evaluation sigma-algebra on the real tempered dual (§1(d), p.3). -/
instance omegaMeasurableSpace (n : ℕ) : MeasurableSpace (Omega n) :=
  ⨆ ψ : RealTest n, MeasurableSpace.comap (fun ω : Omega n => ω ψ) (borel ℝ)

/-- The unnormalized Fourier integral of (1.2), p.3. -/
def paperFourier {n : ℕ} (f : SpectralDomain n → ℂ) (u : SpectralDomain n) : ℂ :=
  ∫ x, Complex.exp (-(Complex.I * (inner ℝ u x : ℂ))) * f x

/-- The positive weight in (1.1), including p=0. -/
def decayWeight {n : ℕ} (p : ℕ) (u : SpectralDomain n) : ℝ :=
  1 / (1 + ‖u‖ ^ 2) ^ p

/-- Extended weighted mass: divergence is infinity, never Bochner's default zero. -/
def weightedMass {n : ℕ} (σ : Measure (SpectralDomain n)) (p : ℕ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (decayWeight p u) ∂σ

/-- The regular positive Borel spectral measures C of (1.1) and Definition 3.1. -/
def InC {n : ℕ} (σ : Measure (SpectralDomain n)) : Prop :=
  σ.Regular ∧ ∃ p : ℕ, weightedMass σ p < ⊤

/-- The spectral quadratic integral, defined before any finiteness assertion. -/
def fourierEnergy {n : ℕ} (σ : Measure (SpectralDomain n)) (f : SpectralDomain n → ℂ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (‖paperFourier f u‖ ^ 2) ∂σ

/-- The real-valued quadratic form; used with explicit finiteness or InC. -/
def spectralQ {n : ℕ} (σ : Measure (SpectralDomain n)) (ψ : ComplexTest n) : ℝ :=
  (fourierEnergy σ ψ).toReal

/-- Include a real test function in the complex-valued functions. -/
def realFunction {n : ℕ} (ψ : RealTest n) : SpectralDomain n → ℂ :=
  fun x => (ψ x : ℂ)

/-- The source's covariance, linear in ψ and conjugate-linear in φ. -/
def spectralPairing {n : ℕ} (σ : Measure (SpectralDomain n)) (ψ φ : ComplexTest n) : ℂ :=
  ∫ u, paperFourier ψ u * conj (paperFourier φ u) ∂σ

/-- All three axioms (3.1)--(3.3), not nonnegativity alone. -/
def PositiveQuadratic {n : ℕ} (q : ComplexTest n → ℝ) : Prop :=
  (∀ ψ, 0 ≤ q ψ) ∧
  (∀ (c : ℂ) ψ, q (c • ψ) = ‖c‖ ^ 2 * q ψ) ∧
  (∀ ψ φ, q (ψ + φ) + q (ψ - φ) = 2 * (q ψ + q φ))

/-- U_t ψ(x)=ψ(x-t), equation (3.4). -/
def testTranslation {n : ℕ} (t : SpectralDomain n) : ComplexTest n →L[ℂ] ComplexTest n :=
  SchwartzMap.compSubConstCLM ℂ t

/-- Actual complex L2 classes for a measure, including the zero measure. -/
abbrev L2 {n : ℕ} (σ : Measure (SpectralDomain n)) := MeasureTheory.Lp ℂ 2 σ

/-- Total L2 packaging. Every use on a paper test is justified by InC or a
conclusion asserting MemLp; the fallback is never used as an integrability test. -/
def l2Class {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    MeasureTheory.Lp ℂ 2 μ := by
  classical
  exact if h : MemLp f 2 μ then h.toLp f else 0

/-- Fourier inclusion into the spectral L2 space. -/
def fourierClass {n : ℕ} (σ : Measure (SpectralDomain n)) (ψ : ComplexTest n) : L2 σ :=
  l2Class σ (paperFourier ψ)

/-- Equation (3.7) after cancellation of its two reciprocal weights. -/
def factorFromW {n : ℕ} {σ : Measure (SpectralDomain n)}
    (W : L2 σ ≃ₗᵢ[ℂ] L2 (volume : Measure (SpectralDomain n))) (ψ : ComplexTest n) :=
  W (fourierClass σ ψ)

/-- Equation (3.6), with Mathlib's inner-product slots reversed to match the source. -/
def HilbertFactor {n : ℕ} (σ : Measure (SpectralDomain n))
    (Q : ComplexTest n →L[ℂ] L2 (volume : Measure (SpectralDomain n))) : Prop :=
  ∀ ψ φ, inner ℂ (Q φ) (Q ψ) = spectralPairing σ ψ φ

/-- A concrete model of the separated spectral completion: close the Fourier image
in L2(σ). Taking the span is harmless because that image is linear on InC. -/
def spectralCompletion {n : ℕ} (σ : Measure (SpectralDomain n)) : Submodule ℂ (L2 σ) :=
  (Submodule.span ℂ (Set.range (fourierClass σ))).topologicalClosure

/-- The canonical image of a test in its separated spectral completion. -/
def spectralVector {n : ℕ} (σ : Measure (SpectralDomain n)) (ψ : ComplexTest n) :
    spectralCompletion σ :=
  ⟨fourierClass σ ψ,
    (Submodule.le_topologicalClosure _)
      (Submodule.subset_span (Set.mem_range_self ψ))⟩

/-- Local totality means density of the COMPLEX LINEAR SPAN of exponentials. -/
def LocallyTotalExponentials {n : ℕ} (σ : Measure (SpectralDomain n)) : Prop :=
  ∀ K : Set (SpectralDomain n), IsCompact K →
    Dense ((Submodule.span ℂ (Set.range (fun t : SpectralDomain n =>
      l2Class (σ.restrict K) (fun u => Complex.exp (Complex.I * (inner ℝ t u : ℂ)))))) :
      Set (L2 (σ.restrict K)))

/-- Definition 4.1, with the ambient norm from L2(dx) and two independent tail indices. -/
def Closable {n : ℕ} (q : ComplexTest n → ℝ) : Prop :=
  ∀ s : ℕ → ComplexTest n,
    Tendsto (fun k => ‖l2Class (volume : Measure (SpectralDomain n)) (s k)‖) atTop (𝓝 0) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, q (s k - s l) < ε) →
    Tendsto (fun k => q (s k)) atTop (𝓝 0)

/-- A law is specified by its real characteristic functional, not complex mixed
covariances. The finite-energy clause makes conversion to real numbers explicit. -/
def CharacteristicLaw {n : ℕ} (σ : Measure (SpectralDomain n)) (μ : Measure (Omega n)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ψ : RealTest n,
    fourierEnergy σ (realFunction ψ) < ⊤ ∧
    (∫ ω, Complex.exp (Complex.I * (ω ψ : ℂ)) ∂μ) =
      Complex.exp (((-(fourierEnergy σ (realFunction ψ)).toReal / 2 : ℝ) : ℂ))

/-- Continuous anti-duals express the source's distribution paired against a
conjugated test. This keeps the first-slot linear source convention explicit. -/
abbrev AntiDual (n : ℕ) := ComplexTest n →L⋆[ℂ] ℂ

/-- The distribution specified by the spectral pairing itself. Its representing
continuous functional exists on InC; that assertion remains a theorem conclusion. -/
def spectralDistribution {n : ℕ} (σ : Measure (SpectralDomain n)) (ψ : ComplexTest n) : AntiDual n := by
  classical
  exact if h : ∃ T : AntiDual n, ∀ φ, T φ = spectralPairing σ ψ φ then h.choose else 0

/-- The actual distributional adjoint product, computed from Q, without a kernel hypothesis. -/
def adjointProduct {n : ℕ}
    (Q : ComplexTest n →L[ℂ] L2 (volume : Measure (SpectralDomain n))) (ψ : ComplexTest n) : AntiDual n :=
  (innerSLFlip ℂ (Q ψ)).comp Q

/-- The covariance kernel of §6 as scalar multiplication operators, for RKHS.OfKernel. -/
def covarianceKernel {n : ℕ} (σ : Measure (SpectralDomain n)) :
    Matrix (RealTest n) (RealTest n) (ℂ →L[ℂ] ℂ) :=
  fun ψ φ =>
    (Complex.exp (((-(fourierEnergy σ (realFunction (ψ - φ))).toReal / 2 : ℝ) : ℂ))) •
      ContinuousLinearMap.id ℂ ℂ

/-- Formula (6.1), on the full complex L2 probability space. -/
def lawFourier {n : ℕ} (μ : Measure (Omega n))
    (f : MeasureTheory.Lp ℂ 2 μ) (ψ : RealTest n) : ℂ :=
  ∫ ω, Complex.exp (-(Complex.I * (ω ψ : ℂ))) * f ω ∂μ

/-- θ_t ω=ω(·-t) as a distribution: θ_t ω(ψ)=ω(ψ(·+t)). -/
def distributionShift {n : ℕ} (t : SpectralDomain n) (ω : Omega n) : Omega n :=
  ω.comp (SchwartzMap.compSubConstCLM ℝ (-t))

/-- Full complex L2 unitaries, including the constants. -/
abbrev KoopmanFamily {n : ℕ} (μ : Measure (Omega n)) :=
  SpectralDomain n → (MeasureTheory.Lp ℂ 2 μ ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 μ)

/-- Measure preservation, group law, and actual pullback on ae classes. -/
def IsKoopman {n : ℕ} (μ : Measure (Omega n)) (U : KoopmanFamily μ) : Prop :=
  (∀ t, MeasurePreserving (distributionShift t) μ μ) ∧
  U 0 = LinearIsometryEquiv.refl ℂ _ ∧
  (∀ t s, U (t + s) = (U t).trans (U s)) ∧
  ∀ t f, (fun ω => (U t f) ω) =ᵐ[μ] (fun ω => f (distributionShift t ω))

/-- Ergodicity for the whole translation group, using measurable sets invariant modulo null sets. -/
def ShiftErgodic {n : ℕ} (μ : Measure (Omega n)) : Prop :=
  ∀ A : Set (Omega n), MeasurableSet A →
    (∀ t : SpectralDomain n, ∀ᵐ ω ∂μ, (distributionShift t ω ∈ A ↔ ω ∈ A)) →
    μ A = 0 ∨ μ A = 1

/-- No nonzero joint frequency, AND the zero eigenspace consists exactly of constants.
For a probability law the constants form a one-dimensional complex space. -/
def TrivialPointSpectrum {n : ℕ} (μ : Measure (Omega n)) (U : KoopmanFamily μ) : Prop :=
  (∀ (a : SpectralDomain n) (f : MeasureTheory.Lp ℂ 2 μ), f ≠ 0 →
    (∀ t, U t f = Complex.exp (Complex.I * (inner ℝ a t : ℂ)) • f) → a = 0) ∧
  (∀ f : MeasureTheory.Lp ℂ 2 μ,
    (∀ t, U t f = f) ↔ ∃ c : ℂ, f = l2Class μ (fun _ => c))

/-- Definition (11.1): q and C are chosen before the arbitrary translation v. -/
def InCb {n : ℕ} (σ : Measure (SpectralDomain n)) : Prop :=
  σ.Regular ∧ ∀ p : ℕ, 1 ≤ p → ∃ q : ℕ, 1 ≤ q ∧ ∃ C : ℝ, 0 < C ∧
    ∀ v : SpectralDomain n,
      (∫⁻ u, ENNReal.ofReal (decayWeight q (u + v)) ∂σ) ≤
        ENNReal.ofReal (C * decayWeight p v)

/-- Extended-valued convolution; the output is not assumed locally finite. -/
def measureConvolution {n : ℕ} (σ τ : Measure (SpectralDomain n)) : Measure (SpectralDomain n) :=
  Measure.map (fun uv : SpectralDomain n × SpectralDomain n => uv.1 + uv.2) (σ.prod τ)

/-- Identify R with one-dimensional Euclidean space without changing Lebesgue normalization. -/
def point1 (x : ℝ) : SpectralDomain 1 :=
  WithLp.toLp 2 (fun _ : Fin 1 => x)

/-- The integer Dirac comb, as a genuine measure. -/
def diracComb : Measure (SpectralDomain 1) :=
  Measure.sum (fun m : ℤ => Measure.dirac (point1 (m : ℝ)))

/-- ℓ²(Z), modeled as L2 of counting measure. -/
abbrev SequenceL2 := MeasureTheory.Lp ℂ 2 (Measure.count : Measure ℤ)

/-- Integer Fourier samples; square summability remains part of Proposition 12.1. -/
def combSamples (ψ : ComplexTest 1) (m : ℤ) : ℂ :=
  paperFourier ψ (point1 (m : ℝ))

/-- The periodization sum from (12.2); the adjoint product has an extra factor 2π. -/
def periodization (ψ : ComplexTest 1) (x : SpectralDomain 1) : ℂ :=
  ∑' m : ℤ, ψ (x + point1 (2 * Real.pi * (m : ℝ)))

/-! Sanity examples pin complete definition bodies; no definition uses sorry. -/

example (x : ℝ) : point1 x 0 = x := rfl

example {n : ℕ} (u : SpectralDomain n) : paperFourier (fun _ : SpectralDomain n => (0 : ℂ)) u = 0 := by
  simp [paperFourier]

example {n : ℕ} (σ : Measure (SpectralDomain n)) :
    fourierEnergy σ (fun _ => (0 : ℂ)) = 0 := by
  simp [fourierEnergy, paperFourier]

example {n : ℕ} (u : SpectralDomain n) : decayWeight 0 u = 1 := by
  simp [decayWeight]

example {n : ℕ} (p : ℕ) : weightedMass (0 : Measure (SpectralDomain n)) p = 0 := by
  simp [weightedMass]

example {n : ℕ} (ψ φ : ComplexTest n) : spectralPairing (0 : Measure (SpectralDomain n)) ψ φ = 0 := by
  simp [spectralPairing]

example {n : ℕ} (ψ : ComplexTest n) : spectralDistribution (0 : Measure (SpectralDomain n)) ψ = 0 := by
  classical
  have h : ∃ T : AntiDual n, ∀ φ, T φ = spectralPairing (0 : Measure (SpectralDomain n)) ψ φ := by
    refine ⟨0, ?_⟩
    intro φ
    simp [spectralPairing]
  unfold spectralDistribution
  rw [dif_pos h]
  ext φ
  simpa [spectralPairing] using h.choose_spec φ

example {n : ℕ} (t x : SpectralDomain n) (ψ : ComplexTest n) : testTranslation t ψ x = ψ (x - t) := rfl

example {n : ℕ} (σ : Measure (SpectralDomain n)) (ψ : ComplexTest n) :
    (spectralVector σ ψ : L2 σ) = fourierClass σ ψ := rfl

example {n : ℕ} (ψ : RealTest n) (t : SpectralDomain n) (ω : Omega n) :
    distributionShift t ω ψ = ω (SchwartzMap.compSubConstCLM ℝ (-t) ψ) := rfl

example {n : ℕ} (Q : ComplexTest n →L[ℂ] L2 (volume : Measure (SpectralDomain n))) (ψ φ : ComplexTest n) :
    adjointProduct Q ψ φ = inner ℂ (Q φ) (Q ψ) := rfl

example {n : ℕ} (σ : Measure (SpectralDomain n)) (ψ : RealTest n) :
    covarianceKernel σ ψ ψ = ContinuousLinearMap.id ℂ ℂ := by
  simp [covarianceKernel, realFunction, fourierEnergy, paperFourier]

example (ψ : ComplexTest 1) (m : ℤ) : combSamples ψ m = paperFourier ψ (point1 (m : ℝ)) := rfl

example (ψ : ComplexTest 1) (x : SpectralDomain 1) :
    periodization ψ x = ∑' m : ℤ, ψ (x + point1 (2 * Real.pi * (m : ℝ))) := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P38


