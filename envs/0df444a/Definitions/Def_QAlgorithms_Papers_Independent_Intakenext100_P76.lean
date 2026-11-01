-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P76
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:47:22.09648+00:00
-- url     : https://prove2.me/theorems/f6c1edbd-fbdb-40b4-8d98-0efe3faaf32e
-- title:
--   Definitions for Second-order coding rates for pure-loss bosonic channels
-- statement:
--   The objects the formalized statements of *Second-order coding rates for pure-loss bosonic channels* (arXiv:1408.5328) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsUnitCoefficientVector`: PDF p.4: unit-vector coefficients on the full countable orthonormal basis. Square summability is explicit; the zero vector is excluded.
--   - `coefficientInner`: PDF p.4: conjugate-linear first argument, as in Mathlib's Hilbert inner product.
--   - `meanOutput`: PDF pp.4,6, (4.1): the density is computed from the channel and input law. Coordinate measurability of pure projectors is the trace-norm Borel convention on this normalized separable-output domain. No finite-support restriction.
--   - `HasSpectralLaw`: PDF p.4: a genuine countable spectral decomposition, allowing zero weights and zero vectors at those weights. The operator is reconstructed, not free data. All nonzero eigenvectors are normalized and mutually orthogonal.
--   - `lowEigenvalueMass`: PDF p.4, (3.3)–(3.6): retained mass of eigenvalues at most 2^(-gamma). The weak inequality is taken from the spectral projector (3.3); eigenvalues at the cutoff are retained, as required by (3.7).
--   - `spectralInfEntropy`: PDF p.4: spectral inf-entropy. On a probability spectrum and 0<=e<1, the defining set is nonempty and bounded above, so the real supremum is valid.
--   - `selfInformationMean`: PDF p.5, (3.12): spectral mean self-information, used only with summability.
--   - `selfInformationVariance`: PDF p.5, (3.13): variance computed independently of the claimed bosonic formula.
--   - `kernelEntropyBits`: Spectral entropy of an actual positive trace-one kernel, in bits, including infinity. Spectral resolutions determine the same value. An empty set of resolutions gives infinity, not zero. PDF pp.4–5, (3.2),(3.12).
--   - `PureCQCode`: PDF p.5: finite nonempty uniform messages, deterministic encoder and one joint POVM on the entire output system. There is no oracle-dependent decoder.
--   - `pureBornProbability`: PDF p.5: Born probability for a normalized vector and bounded effect. Inner row sums and the outer Hilbert pairing converge absolutely on that domain.
--   - `pureCQAverageError`: PDF p.5, (3.15): average, not maximal, message error.
--   - `logMaxCodeSize`: PDF p.5, (3.16): supremum of achievable log cardinalities. EReal preserves an infinite unrestricted code size; all witnesses remain actual finite codes.
--   - `HasFiniteCode`: An actual deterministic finite code attaining a real lower threshold.
--   - `productPureCQChannel`: PDF p.9, (5.1): exact tensor-product pure outputs, in the full product basis.
--   - `productSpectrum`: PDF p.9: iid eigenvalue law of rho tensor n, with no finite truncation.
--   - `thermalPhotonProbability`: PDF p.10, (6.5): complete number-diagonal thermal spectrum, including vacuum.
--   - `thermalDispersion`: PDF pp.3,10: scalar thermal dispersion, explicitly extended to vacuum. This is distinct from selfInformationVariance, to which the theorem equates it.
--   - `heterodyneDispersion`: PDF p.11, (6.12), bits squared: log2(e)=1/ln(2).
--   - `coherentChannel`: PDF p.10, (6.2): identity-transmissivity coherent-state cq channel.
--   - `photonLeakage`: PDF p.11: leakage outside the total-photon subspace, averaged over uniform messages; the cutoff is ceil(n NS), not a separate cutoff on each mode.
--   - `bpskAverage`: PDF p.13: actual equiprobable BPSK average density, not its entropy formula.
--   - `bpskHolevoBits`: PDF p.13, (6.14): scalar BPSK Holevo expression in bits.
--   - `bpskHolevoNats`: PDF p.13: same scalar expression converted to nats.
--   - `thermalEntropyNats`: PDF p.13, (6.15): unconstrained-modulation Holevo expression in nats.
--   - `dolinarCrossover`: PDF p.13, (6.17): exact binary symmetric crossover probability.
--   - `dolinarNats`: PDF p.13: scalar BPSK/Dolinar capacity in nats, independently of the expansion.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, https://arxiv.org/abs/1408.5328v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

/-!
arXiv:1408.5328v3. Countable coordinates describe completed separable Hilbert
spaces, including finite dimensions. Infinite matrices below are coefficient
arrays, never finite cutoffs. Positive finite forms and POVM completeness imply
bounded effects on l2; all Born pairings are iterated sums, not an unordered
non-absolutely-convergent double series. Distinct new definitions are paper-local;
accepted definitions are imported as explicitly required by the repair instruction.
The three source deferrals and the printed sign correction are documented in
the unit artifacts. Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)
open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)
open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.4: unit-vector coefficients on the full countable orthonormal basis.
Square summability is explicit; the zero vector is excluded. -/
def IsUnitCoefficientVector {I : Type} (u : I → ℂ) : Prop :=
  Summable (fun i => Complex.normSq (u i)) ∧ ∑' i, Complex.normSq (u i) = 1

/-- PDF p.4: conjugate-linear first argument, as in Mathlib's Hilbert inner product. -/
def coefficientInner {I : Type} (u v : I → ℂ) : ℂ :=
  ∑' i, star (u i) * v i

/-- PDF pp.4,6, (4.1): the density is computed from the channel and input law.
Coordinate measurability of pure projectors is the trace-norm Borel convention
on this normalized separable-output domain. No finite-support restriction. -/
def meanOutput {X : Type*} {I : Type} [MeasurableSpace X]
    (W : X → I → ℂ) (mu : Measure X) : Matrix I I ℂ :=
  fun a b => ∫ x, Matrix.vecMulVec (W x) (star (W x)) a b ∂mu

/-- PDF p.4: a genuine countable spectral decomposition, allowing zero weights
and zero vectors at those weights. The operator is reconstructed, not free data.
All nonzero eigenvectors are normalized and mutually orthogonal. -/
def HasSpectralLaw {I : Type} {J : Type*} (rho : Matrix I I ℂ) (p : J → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ Summable p ∧ (∑' j, p j) = 1 ∧
    ∃ u : J → I → ℂ,
      (∀ j, 0 < p j → IsUnitCoefficientVector (u j)) ∧
      (∀ j k, j ≠ k → 0 < p j → 0 < p k → coefficientInner (u j) (u k) = 0) ∧
      ∀ a b, rho a b = ∑' j, (p j : ℂ) * Matrix.vecMulVec (u j) (star (u j)) a b

/-- PDF p.4, (3.3)–(3.6): retained mass of eigenvalues at most 2^(-gamma).
The weak inequality is taken from the spectral projector (3.3); eigenvalues
at the cutoff are retained, as required by (3.7). -/
def lowEigenvalueMass {J : Type*} (p : J → ℝ) (gamma : ℝ) : ℝ :=
  ∑' j, if p j ≤ (2 : ℝ) ^ (-gamma) then p j else 0

/-- PDF p.4: spectral inf-entropy. On a probability spectrum and 0<=e<1,
the defining set is nonempty and bounded above, so the real supremum is valid. -/
def spectralInfEntropy {J : Type*} (p : J → ℝ) (e : ℝ) : ℝ :=
  sSup {gamma : ℝ | 1 - e ≤ lowEigenvalueMass p gamma}

/-- PDF p.5, (3.12): spectral mean self-information, used only with summability. -/
def selfInformationMean {J : Type*} (p : J → ℝ) : ℝ :=
  ∑' j, p j * (-logTwo (p j))

/-- PDF p.5, (3.13): variance computed independently of the claimed bosonic formula. -/
def selfInformationVariance {J : Type*} (p : J → ℝ) : ℝ :=
  ∑' j, p j * (-logTwo (p j) - selfInformationMean p) ^ 2

/-- Spectral entropy of an actual positive trace-one kernel, in bits, including
infinity. Spectral resolutions determine the same value. An empty set of
resolutions gives infinity, not zero. PDF pp.4–5, (3.2),(3.12). -/
def kernelEntropyBits {I : Type} (rho : Matrix I I ℂ) : ℝ≥0∞ :=
  sInf {z : ℝ≥0∞ | ∃ p : ℕ → ℝ, HasSpectralLaw rho p ∧
    z = ∑' j, ENNReal.ofReal (-p j * logTwo (p j))}

/-- PDF p.5: finite nonempty uniform messages, deterministic encoder and one
joint POVM on the entire output system. There is no oracle-dependent decoder. -/
structure PureCQCode (X : Type*) (I : Type) (M : ℕ) where
  nonempty : 0 < M
  encode : Fin M → X
  effect : Fin M → Matrix I I ℂ
  positive : ∀ m, PositiveKernel (effect m)
  complete : ∀ a b, (∑ m, effect m a b) = if a = b then 1 else 0

/-- PDF p.5: Born probability for a normalized vector and bounded effect.
Inner row sums and the outer Hilbert pairing converge absolutely on that domain. -/
def pureBornProbability {I : Type} (u : I → ℂ) (E : Matrix I I ℂ) : ℝ :=
  (∑' a, star (u a) * (∑' b, E a b * u b)).re

/-- PDF p.5, (3.15): average, not maximal, message error. -/
def pureCQAverageError {X : Type*} {I : Type} {M : ℕ} (W : X → I → ℂ) (c : PureCQCode X I M) : ℝ :=
  1 - (∑ m, pureBornProbability (W (c.encode m)) (c.effect m)) / (M : ℝ)

/-- PDF p.5, (3.16): supremum of achievable log cardinalities. EReal preserves
an infinite unrestricted code size; all witnesses remain actual finite codes. -/
def logMaxCodeSize {X : Type*} {I : Type} (W : X → I → ℂ) (e : ℝ) : EReal :=
  sSup {r : EReal | ∃ (M : ℕ) (c : PureCQCode X I M),
    pureCQAverageError W c ≤ e ∧ r = (logTwo (M : ℝ) : EReal)}

/-- An actual deterministic finite code attaining a real lower threshold. -/
def HasFiniteCode {X : Type*} {I : Type} (W : X → I → ℂ) (e R : ℝ) : Prop :=
  ∃ (M : ℕ) (c : PureCQCode X I M), pureCQAverageError W c ≤ e ∧ R ≤ logTwo (M : ℝ)

/-- PDF p.9, (5.1): exact tensor-product pure outputs, in the full product basis. -/
def productPureCQChannel {X : Type*} {I : Type} (W : X → I → ℂ) (n : ℕ) :
    (Fin n → X) → (Fin n → I) → ℂ :=
  fun x a => ∏ i, W (x i) (a i)

/-- PDF p.9: iid eigenvalue law of rho tensor n, with no finite truncation. -/
def productSpectrum {J : Type*} (p : J → ℝ) (n : ℕ) : (Fin n → J) → ℝ :=
  fun a => ∏ i, p (a i)

/-- PDF p.10, (6.5): complete number-diagonal thermal spectrum, including vacuum. -/
def thermalPhotonProbability (x : ℝ) (k : ℕ) : ℝ := x ^ k / (x + 1) ^ (k + 1)

/-- PDF pp.3,10: scalar thermal dispersion, explicitly extended to vacuum.
This is distinct from selfInformationVariance, to which the theorem equates it. -/
def thermalDispersion (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * (x + 1) * (logTwo (x + 1) - logTwo x) ^ 2

/-- PDF p.11, (6.12), bits squared: log2(e)=1/ln(2). -/
def heterodyneDispersion (x : ℝ) : ℝ :=
  x * (x + 2) * (1 / Real.log 2) ^ 2 / (x + 1) ^ 2

/-- PDF p.10, (6.2): identity-transmissivity coherent-state cq channel. -/
def coherentChannel (n : ℕ) : (Fin n → ℂ) → (Fin n → ℕ) → ℂ :=
  productPureCQChannel coherentCoefficient n

/-- PDF p.11: leakage outside the total-photon subspace, averaged over uniform
messages; the cutoff is ceil(n NS), not a separate cutoff on each mode. -/
def photonLeakage {n M : ℕ} (c : PureCQCode (Fin n → ℂ) (Fin n → ℕ) M) (NS : ℝ) : ℝ :=
  (∑ m, ∑' a : Fin n → ℕ,
    if ⌈(n : ℝ) * NS⌉₊ < ∑ i, a i then
      Complex.normSq (coherentChannel n (c.encode m) a) else 0) / (M : ℝ)

/-- PDF p.13: actual equiprobable BPSK average density, not its entropy formula. -/
def bpskAverage (alpha : ℂ) : Matrix ℕ ℕ ℂ :=
  fun a b => (Matrix.vecMulVec (coherentCoefficient alpha) (star (coherentCoefficient alpha)) a b +
    Matrix.vecMulVec (coherentCoefficient (-alpha)) (star (coherentCoefficient (-alpha))) a b) / 2

/-- PDF p.13, (6.14): scalar BPSK Holevo expression in bits. -/
def bpskHolevoBits (x : ℝ) : ℝ :=
  QAlgorithms.binEntropy2 ((1 - Real.exp (-2 * x)) / 2)

/-- PDF p.13: same scalar expression converted to nats. -/
def bpskHolevoNats (x : ℝ) : ℝ := Real.log 2 * bpskHolevoBits x

/-- PDF p.13, (6.15): unconstrained-modulation Holevo expression in nats. -/
def thermalEntropyNats (x : ℝ) : ℝ := Real.log 2 * thermalEntropy x

/-- PDF p.13, (6.17): exact binary symmetric crossover probability. -/
def dolinarCrossover (x : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - Real.exp (-4 * x))) / 2

/-- PDF p.13: scalar BPSK/Dolinar capacity in nats, independently of the expansion. -/
def dolinarNats (x : ℝ) : ℝ :=
  Real.log 2 * (1 - QAlgorithms.binEntropy2 (dolinarCrossover x))

/-! Sanity checks on zero weights, zero energy, tensor products and normalization. -/

example : logTwo 1 = 0 := by simp [logTwo]

example : ¬ IsUnitCoefficientVector (fun _ : ℕ => (0 : ℂ)) := by simp [IsUnitCoefficientVector]

example : Matrix.vecMulVec (fun _ : ℕ => (0 : ℂ))
    (star (fun _ : ℕ => (0 : ℂ))) = 0 := by ext a b; simp [Matrix.vecMulVec]

example : IsUnitCoefficientVector (fun k : ℕ => if k = 0 then (1 : ℂ) else 0) := by
  constructor
  · apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    have hk0 : k ≠ 0 := by simpa using hk
    simp [hk0]
  · simp

example : pureBornProbability (fun _ : Fin 1 => (1 : ℂ)) (fun _ _ => (1 : ℂ)) = 1 := by
  simp [pureBornProbability]

example : thermalPhotonProbability 0 0 = 1 := by simp [thermalPhotonProbability]

example (k : ℕ) : thermalPhotonProbability 0 (k + 1) = 0 := by simp [thermalPhotonProbability]

example : thermalEntropy 0 = 0 := by simp [thermalEntropy, logTwo]

example : thermalDispersion 0 = 0 := by simp [thermalDispersion]

example : heterodyneDispersion 0 = 0 := by simp [heterodyneDispersion]

example : coherentCoefficient 0 0 = 1 := by simp [coherentCoefficient]

example : bpskHolevoBits 0 = 0 := by
  simp [bpskHolevoBits, QAlgorithms.binEntropy2]

example : dolinarCrossover 0 = 1 / 2 := by simp [dolinarCrossover]

example : dolinarNats 0 = 0 := by
  rw [dolinarNats, show dolinarCrossover 0 = 1 / 2 by simp [dolinarCrossover]]
  have hb : QAlgorithms.binEntropy2 (1 / 2) = 1 := by
    rw [QAlgorithms.binEntropy2, show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
      Real.binEntropy_two_inv]
    exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [hb]
  simp

example {J : Type*} (p : J → ℝ) (a : Fin 0 → J) : productSpectrum p 0 a = 1 := by
  simp [productSpectrum]

example {X : Type*} {I : Type} (W : X → I → ℂ) (x : Fin 0 → X) (a : Fin 0 → I) :
    productPureCQChannel W 0 x a = 1 := by simp [productPureCQChannel]

end QAlgorithms.Papers.Independent.Intakenext100.P76


