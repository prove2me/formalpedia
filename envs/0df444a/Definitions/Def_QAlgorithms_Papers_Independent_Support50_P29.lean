-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P29
-- name    : QAlgorithms_Papers_Independent_Support50_P29
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:13:11.5513+00:00
-- url     : https://prove2.me/theorems/849507a5-7bae-45e7-af6a-5e83cc01d05e
-- title:
--   Definitions for Sending Quantum Information with Gaussian States
-- statement:
--   The objects the formalized statements of *Sending Quantum Information with Gaussian States* (arXiv:quant-ph/9809022) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `canonicalCommutation`: PDF pp.4-5: grouped physical commutation matrix, never the cocycle matrix.
--   - `referenceCoordinateSwap`: PDF p.6: reference coordinates exchange q and p, reversing the CCR form.
--   - `physicalWeyl`: PDF p.4: normalized regular irreducible Weyl system in physical units.
--   - `centeredCharacteristic`: PDF p.5: characteristic of a centered Gaussian, for either block ordering.
--   - `GaussianCovariancePhysical`: PDF p.5, (2.3): symmetry and the non-strict matrix uncertainty condition.
--   - `CenteredGaussianWithCovariance`: PDF p.5: an actual normalized Gaussian density, with its specified covariance.
--   - `SimilarityData`: PDF pp.5-6: similarity diagonalization, without a normality assumption.
--   - `similarityFunction`: PDF p.5: spectral matrix function in a similarity eigenbasis. The choice is irrelevant on diagonalizable matrices, including repeated eigenvalues. On a nondiagonalizable matrix the total extension is zero; the source targets conclude diagonalizability and use this function only on diagonalizable matrices.
--   - `realSpectralSqrt`: PDF p.6: principal nonnegative spectral square root of a real matrix similar to a nonnegative diagonal matrix. Entrywise real part recovers the real matrix. It is not the singular-value square root of M* M.
--   - `entropyMatrix`: PDF p.6, (2.6): g(abs M-I/2), using the source's similarity calculus.
--   - `purificationCovariance`: PDF pp.6-7: the explicitly prescribed reflected purification covariance.
--   - `reflectedDelta`: PDF p.7: the commutation matrix is diag(Delta,-Delta).
--   - `jointCharacteristic`: PDF p.6: actual tensor Weyl pairing, with the reference CCR reflected.
--   - `realify`: PDF p.7: realification on all complex matrices, not an alleged Hermitian algebra.
--   - `shuffle`: PDF pp.7-8: (q1;p1;q2;p2) to the realification order (q1;q2;p1;p2).
--   - `gaugeCovariance`: PDF p.7: occupation-matrix covariance in grouped real coordinates.
--   - `gaugePurificationMatrix`: PDF p.8, (3.8): the two-by-two block complex representative.
--   - `outputNumber`: PDF p.9: thermal output occupation, with the p.10 identity endpoint.
--   - `exchangeOutput`: PDF p.9: the actual extended output on the normalized Schmidt purification.
--   - `thermalCoherentInformationNats`: PDF p.10: coherent information in nats, as a difference of actual entropies. Its use below includes conclusions that both extended entropies are finite.
--   - `exchangeCovariance`: PDF p.9: the full reflected output covariance, in subsystem block order.
--   - `jointFockCharacteristic`: PDF pp.8-9: actual Fock Weyl pairing; the reference uses (p,q).
--   - `oneModeRealification`: PDF p.9: two-by-two complex matrix, reindexed into subsystem real order.
-- source:
--   Sending Quantum Information with Gaussian States, arXiv:quant-ph/9809022v1, https://arxiv.org/abs/quant-ph/9809022v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49

/-! Holevo, quant-ph/9809022v1. Full separable oscillator Hilbert spaces,
normalized trace-class states, natural logarithms, and reflected reference CCR.
Source corrections are documented in the unit's moderation notes and HARD ledger.
Mechanical compilation and independent moderation are pending the batch handoff. -/

noncomputable section

open Filter
open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P29

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma complexify)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity rankOne productCoeff tensorApply IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Frontier30.P10 (WeylSystem)
open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight PureDensity)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (tracePair thermalInput thermalPurificationDensity vacuumChannel exchangeMatrix RealizedDensity)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-! These source-specific adapters have distinct names because the accepted
same-short-name definitions do not have the same meaning. Information100.P56.delta
is a finite cq entropy difference; Claimed50.P44.reflect is a one-mode momentum
sign matrix, rather than the grouped q/p exchange used here. Claimed50.P19/P30
PhysicalCovariance use interleaved vacuum-I units; Frontier30.P14.CenteredGaussian
is an existential one-mode covariance predicate. Information100.P22/P39
coherentInformation use finite registers, whereas the present difference uses
extended nats entropies of full-Fock outputs. The underlying canonical sigma,
Weyl system, density, channel, and entropy definitions remain accepted imports. -/

/-- PDF pp.4-5: grouped physical commutation matrix, never the cocycle matrix. -/
def canonicalCommutation (s : ℕ) (hbar : ℝ) : Matrix (Phase s) (Phase s) ℝ := hbar • sigma s

/-- PDF p.6: reference coordinates exchange q and p, reversing the CCR form. -/
def referenceCoordinateSwap {s : ℕ} (z : Phase s → ℝ) : Phase s → ℝ :=
  Sum.elim (fun j => z (Sum.inr j)) (fun j => z (Sum.inl j))

/-- PDF p.4: normalized regular irreducible Weyl system in physical units. -/
def physicalWeyl {I : Type} {s : ℕ} (hbar : ℝ)
    (W : WeylSystem (Hilbert I) s) (z : Phase s → ℝ) : Hilbert I →L[ℂ] Hilbert I :=
  (W.operator (fun j => Real.sqrt hbar * z j)).toLinearIsometry.toContinuousLinearMap

/-- PDF p.5: characteristic of a centered Gaussian, for either block ordering. -/
def centeredCharacteristic {F : Type} [Fintype F]
    (alpha : Matrix F F ℝ) (z : F → ℝ) : ℂ :=
  Complex.exp (-((dotProduct z (alpha.mulVec z) / 2 : ℝ) : ℂ))

/-- PDF p.5, (2.3): symmetry and the non-strict matrix uncertainty condition. -/
def GaussianCovariancePhysical {s : ℕ} (hbar : ℝ)
    (alpha : Matrix (Phase s) (Phase s) ℝ) : Prop :=
  alpha.transpose = alpha ∧
    (complexify alpha - (Complex.I / 2) • complexify (canonicalCommutation s hbar)).PosSemidef

/-- PDF p.5: an actual normalized Gaussian density, with its specified covariance. -/
def CenteredGaussianWithCovariance {I : Type} {s : ℕ} (hbar : ℝ)
    (W : WeylSystem (Hilbert I) s) (rho : State I)
    (alpha : Matrix (Phase s) (Phase s) ℝ) : Prop :=
  GaussianCovariancePhysical hbar alpha ∧ ∀ z,
    tracePair rho.coefficients (operatorCoeff (physicalWeyl hbar W z)) =
      centeredCharacteristic alpha z

/-- PDF pp.5-6: similarity diagonalization, without a normality assumption. -/
def SimilarityData {F : Type} [Fintype F] [DecidableEq F]
    (M P : Matrix F F ℂ) (d : F → ℂ) : Prop :=
  IsUnit P ∧ M = P * Matrix.diagonal d * P⁻¹

/-- PDF p.5: spectral matrix function in a similarity eigenbasis.
The choice is irrelevant on diagonalizable matrices, including repeated eigenvalues.
On a nondiagonalizable matrix the total extension is zero; the source targets
conclude diagonalizability and use this function only on diagonalizable matrices. -/
def similarityFunction {F : Type} [Fintype F] [DecidableEq F]
    (M : Matrix F F ℂ) (f : ℂ → ℂ) : Matrix F F ℂ :=
  if h : ∃ P d, SimilarityData M P d then
    let P := h.choose
    let d := h.choose_spec.choose
    P * Matrix.diagonal (fun j => f (d j)) * P⁻¹
  else 0

/-- PDF p.6: principal nonnegative spectral square root of a real matrix
similar to a nonnegative diagonal matrix. Entrywise real part recovers the real
matrix. It is not the singular-value square root of M* M. -/
def realSpectralSqrt {F : Type} [Fintype F] [DecidableEq F]
    (M : Matrix F F ℝ) : Matrix F F ℝ :=
  fun i j => (similarityFunction (complexify M) (fun z => (Real.sqrt z.re : ℂ)) i j).re

/-- PDF p.6, (2.6): g(abs M-I/2), using the source's similarity calculus. -/
def entropyMatrix {F : Type} [Fintype F] [DecidableEq F]
    (M : Matrix F F ℂ) : Matrix F F ℂ :=
  similarityFunction M (fun z => (thermalEntropy (‖z‖ - 1 / 2) : ℂ))

/-- PDF pp.6-7: the explicitly prescribed reflected purification covariance. -/
def purificationCovariance {s : ℕ} (hbar : ℝ)
    (alpha : Matrix (Phase s) (Phase s) ℝ) :
    Matrix (Phase s ⊕ Phase s) (Phase s ⊕ Phase s) ℝ :=
  let A := (canonicalCommutation s hbar)⁻¹ * alpha
  let B := canonicalCommutation s hbar * realSpectralSqrt (-(A ^ 2) - (1 / 4 : ℝ) • 1)
  Matrix.fromBlocks alpha B (-B) alpha

/-- PDF p.7: the commutation matrix is diag(Delta,-Delta). -/
def reflectedDelta (s : ℕ) (hbar : ℝ) :
    Matrix (Phase s ⊕ Phase s) (Phase s ⊕ Phase s) ℝ :=
  Matrix.fromBlocks (canonicalCommutation s hbar) 0 0 (-canonicalCommutation s hbar)

/-- PDF p.6: actual tensor Weyl pairing, with the reference CCR reflected. -/
def jointCharacteristic {I J : Type} {s : ℕ} (hbar : ℝ)
    (W : WeylSystem (Hilbert I) s) (V : WeylSystem (Hilbert J) s)
    (X : Matrix (I × J) (I × J) ℂ) (z : (Phase s ⊕ Phase s) → ℝ) : ℂ :=
  tracePair X (productCoeff
    (operatorCoeff (physicalWeyl hbar W (fun i => z (Sum.inl i))))
    (operatorCoeff (physicalWeyl hbar V (referenceCoordinateSwap (fun i => z (Sum.inr i))))))

/-- PDF p.7: realification on all complex matrices, not an alleged Hermitian algebra. -/
def realify {F : Type} (M : Matrix F F ℂ) : Matrix (F ⊕ F) (F ⊕ F) ℝ :=
  Matrix.fromBlocks (fun i j => (M i j).re) (fun i j => -(M i j).im)
    (fun i j => (M i j).im) (fun i j => (M i j).re)

/-- PDF pp.7-8: (q1;p1;q2;p2) to the realification order (q1;q2;p1;p2). -/
def shuffle {s : ℕ} : Phase s ⊕ Phase s → (Fin s ⊕ Fin s) ⊕ (Fin s ⊕ Fin s)
  | Sum.inl (Sum.inl j) => Sum.inl (Sum.inl j)
  | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
  | Sum.inr (Sum.inl j) => Sum.inl (Sum.inr j)
  | Sum.inr (Sum.inr j) => Sum.inr (Sum.inr j)

/-- PDF p.7: occupation-matrix covariance in grouped real coordinates. -/
def gaugeCovariance {s : ℕ} (hbar : ℝ) (N : Matrix (Fin s) (Fin s) ℂ) :
    Matrix (Phase s) (Phase s) ℝ := hbar • realify (N + (1 / 2 : ℂ) • 1)

/-- PDF p.8, (3.8): the two-by-two block complex representative. -/
def gaugePurificationMatrix {s : ℕ} (N : Matrix (Fin s) (Fin s) ℂ) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  let C := similarityFunction (N ^ 2 + N) (fun z => (Real.sqrt z.re : ℂ))
  Matrix.fromBlocks (Complex.I • (N + (1 / 2 : ℂ) • 1)) C C
    (-Complex.I • (N + (1 / 2 : ℂ) • 1))

/-- PDF p.9: thermal output occupation, with the p.10 identity endpoint. -/
def outputNumber (N k : ℝ) : ℝ :=
  if k ≤ 1 then k ^ 2 * N else k ^ 2 * N + (k ^ 2 - 1)

/-- PDF p.9: the actual extended output on the normalized Schmidt purification. -/
def exchangeOutput (N k : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  tensorApply (vacuumChannel k) (thermalPurificationDensity N)

/-- PDF p.10: coherent information in nats, as a difference of actual entropies.
Its use below includes conclusions that both extended entropies are finite. -/
def thermalCoherentInformationNats (N k : ℝ) : ℝ :=
  (extendedEntropyNats (vacuumChannel k (thermalInput N))).toReal -
    (extendedEntropyNats (exchangeOutput N k)).toReal

/-- PDF p.9: the full reflected output covariance, in subsystem block order. -/
def exchangeCovariance (hbar N k : ℝ) :
    Matrix (Phase 1 ⊕ Phase 1) (Phase 1 ⊕ Phase 1) ℝ :=
  let B := (k * Real.sqrt (N * (N + 1))) • canonicalCommutation 1 hbar
  Matrix.fromBlocks ((hbar * (outputNumber N k + 1 / 2)) • 1) B (-B)
    ((hbar * (N + 1 / 2)) • 1)

/-- PDF pp.8-9: actual Fock Weyl pairing; the reference uses (p,q). -/
def jointFockCharacteristic (hbar : ℝ) (X : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ)
    (z : (Phase 1 ⊕ Phase 1) → ℝ) : ℂ :=
  let u : ℂ := (z (Sum.inl (Sum.inl 0)) : ℂ) +
    Complex.I * (z (Sum.inl (Sum.inr 0)) : ℂ)
  let v : ℂ := (z (Sum.inr (Sum.inr 0)) : ℂ) +
    Complex.I * (z (Sum.inr (Sum.inl 0)) : ℂ)
  tracePair X (productCoeff
    (displacementMatrix (Complex.I * (Real.sqrt (hbar / 2) : ℂ) * u))
    (displacementMatrix (Complex.I * (Real.sqrt (hbar / 2) : ℂ) * v)))

/-- PDF p.9: two-by-two complex matrix, reindexed into subsystem real order. -/
def oneModeRealification (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Phase 1 ⊕ Phase 1) (Phase 1 ⊕ Phase 1) ℝ :=
  let index : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  let C : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := M.submatrix index index
  (realify C).submatrix shuffle shuffle

/-! Definition sanity examples. No source theorem is proved in this draft. -/

example : thermalEntropy 0 = 0 := by simp [thermalEntropy]

example {s : ℕ} (z : Phase s → ℝ) : referenceCoordinateSwap (referenceCoordinateSwap z) = z := by
  funext i
  cases i <;> rfl

example (hbar : ℝ) : canonicalCommutation 1 hbar (Sum.inl 0) (Sum.inr 0) = hbar := by
  simp [canonicalCommutation, sigma]

example {F : Type} [Fintype F] [DecidableEq F] (M : Matrix F F ℂ) :
    similarityFunction M (fun _ => 0) = 0 := by
  unfold similarityFunction
  split <;> simp

example (N : ℝ) : outputNumber N 1 = N := by simp [outputNumber]

example (hbar : ℝ) : exchangeCovariance hbar 0 0 =
    Matrix.fromBlocks ((hbar * (1 / 2)) • (1 : Matrix (Phase 1) (Phase 1) ℝ))
      0 0 ((hbar * (1 / 2)) • (1 : Matrix (Phase 1) (Phase 1) ℝ)) := by
  simp [exchangeCovariance, outputNumber]

end QAlgorithms.Papers.Independent.Support50.P29


