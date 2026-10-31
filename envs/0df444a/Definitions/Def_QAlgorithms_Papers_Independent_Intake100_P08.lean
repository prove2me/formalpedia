-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P08
-- name    : QAlgorithms_Papers_Independent_Intake100_P08
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:48:21.197182+00:00
-- url     : https://prove2.me/theorems/28b4ea45-5561-42c9-a116-fa3da4d867b4
-- title:
--   Definitions for Discrimination of the binary coherent signal: Gaussian-operation limit and simple non-Gaussian near-optimal receivers
-- statement:
--   The objects the formalized statements of *Discrimination of the binary coherent signal: Gaussian-operation limit and simple non-Gaussian near-optimal receivers* (arXiv:0706.1038) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `signalAmplitude`: PDF pp.1,4: known real phase-aligned amplitude; true labels plus.
--   - `photonLaw`: PDF p.4, Eq.(18): the full number distribution of an oscillator vector. Only normalized vectors are used as states; no photon-number cutoff.
--   - `countNoClick`: PDF p.4, Eq.(18): diagonal on/off effect evaluated on a number law. For physical parameters and normalized laws the series is summable, as the headline statements explicitly assert for every participating law.
--   - `receiverError`: PDF p.5, Eq.(19): average Bayesian error, with equal priors and fixed on/off decoding. The same fixed preprocessing receives both possible inputs.
--   - `displacementError`: PDF p.5, Eqs.(23)--(24): the actual completed-space displacement before one detector. This is defined by the experiment, not its claimed scalar formula. The theorem concludes the realization guards of the accepted operator.
--   - `IsGaussianUnitary`: PDF pp.1,5: all single-mode affine Gaussian unitaries, including squeezing. The genuine Hilbert-space unitary intertwines the actual Weyl displacements by an arbitrary real-linear symplectic map and a real-linear phase. The latter retains all affine displacements. This bounded Weyl characterization avoids exponentiating a totalized unbounded quadratic generator.
--   - `bpskHomodyneError`: PDF p.1: erfc(sqrt(2) alpha)/2 written as its convergent Gaussian tail. This is the equal-prior error of the exact q-homodyne spectral outcome law, whose coherent signals have means plus or minus sqrt(2) alpha and physical variance 1/2. The accepted Dependency50.P17.homodyneError is instead block-code decoding error for a two-sender channel; it is a distinct concept and is not reused.
--   - `poissonPhotonLaw`: PDF p.5, preceding Eq.(26): the infinite Poisson photon-number law. Nonnegative intensity and normalization are concluded below, not assumed.
--   - `mismatchIntensity`: PDF p.5, Eq.(25): total intensity after interference, including the noninterfering portion. delta is the output displacement, possibly complex.
--   - `imperfectError`: PDF pp.5--6, Eqs.(25)--(26): physical Poisson laws and the same fixed on/off decoding. No optimized displacement or error formula is assumed.
--   - `localOscillator`: PDF p.5: finite-beamsplitter local oscillator for output displacement delta. Used only for tau<1. tau=1 is the ideal displacement limit, not this division.
-- source:
--   Discrimination of the binary coherent signal: Gaussian-operation limit and simple non-Gaussian near-optimal receivers, arXiv:0706.1038v3, https://arxiv.org/abs/0706.1038v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Takeoka--Sasaki, arXiv:0706.1038v3. The oscillator is the completed countable
Fock space. Three Section III results are stated; HARD.md accounts for all
other nodes. Equal priors, fixed decoding off -> minus / on -> plus, and no
feedback are built into receiverError. The apparatus never receives the sign.
The homodyne comparison uses its exact coherent-state spectral outcome law,
with [q,p]=i, means plus or minus sqrt(2) alpha and variance 1/2. No infinitely squeezed
vector or cutoff is introduced. Compilation and independent moderation pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P08

open MeasureTheory
open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock fockKet coherentKet coherentCoefficient CoherentRealized
   displacement DisplacementRealized)

/-- PDF pp.1,4: known real phase-aligned amplitude; true labels plus. -/
def signalAmplitude (alpha : ℝ) (plus : Bool) : ℂ :=
  if plus then (alpha : ℂ) else -(alpha : ℂ)

/-- PDF p.4, Eq.(18): the full number distribution of an oscillator vector.
Only normalized vectors are used as states; no photon-number cutoff. -/
def photonLaw (psi : Fock) (n : ℕ) : ℝ := Complex.normSq (psi n)

/-- PDF p.4, Eq.(18): diagonal on/off effect evaluated on a number law.
For physical parameters and normalized laws the series is summable, as the
headline statements explicitly assert for every participating law. -/
def countNoClick (eta nu : ℝ) (law : ℕ → ℝ) : ℝ :=
  Real.exp (-nu) * ∑' n : ℕ, (1 - eta) ^ n * law n

/-- PDF p.5, Eq.(19): average Bayesian error, with equal priors and fixed
on/off decoding. The same fixed preprocessing receives both possible inputs. -/
def receiverError (alpha eta nu : ℝ) (preprocess : Fock → Fock) : ℝ :=
  (countNoClick eta nu (photonLaw (preprocess (coherentKet (signalAmplitude alpha true)))) +
    1 - countNoClick eta nu
      (photonLaw (preprocess (coherentKet (signalAmplitude alpha false))))) / 2

/-- PDF p.5, Eqs.(23)--(24): the actual completed-space displacement before
one detector. This is defined by the experiment, not its claimed scalar formula.
The theorem concludes the realization guards of the accepted operator. -/
def displacementError (alpha eta nu : ℝ) (delta : ℂ) : ℝ :=
  receiverError alpha eta nu (fun psi => displacement delta psi)

/-- PDF pp.1,5: all single-mode affine Gaussian unitaries, including squeezing.
The genuine Hilbert-space unitary intertwines the actual Weyl displacements by
an arbitrary real-linear symplectic map and a real-linear phase. The latter
retains all affine displacements. This bounded Weyl characterization avoids
exponentiating a totalized unbounded quadratic generator. -/
def IsGaussianUnitary (U : Fock ≃ₗᵢ[ℂ] Fock) : Prop :=
  ∃ S : ℂ →ₗ[ℝ] ℂ,
    (∀ z w : ℂ, (star (S z) * S w).im = (star z * w).im) ∧
    ∃ ell : ℂ →ₗ[ℝ] ℝ, ∀ (z : ℂ) (psi : Fock),
      U (displacement z psi) =
        Complex.exp (Complex.I * (ell z : ℂ)) • displacement (S z) (U psi)

/-- PDF p.1: erfc(sqrt(2) alpha)/2 written as its convergent Gaussian tail.
This is the equal-prior error of the exact q-homodyne spectral outcome law,
whose coherent signals have means plus or minus sqrt(2) alpha and physical variance 1/2.
The accepted Dependency50.P17.homodyneError is instead block-code decoding
error for a two-sender channel; it is a distinct concept and is not reused. -/
def bpskHomodyneError (alpha : ℝ) : ℝ :=
  (∫ x : ℝ in Set.Ici (Real.sqrt 2 * alpha), Real.exp (-(x ^ 2))) / Real.sqrt Real.pi

/-- PDF p.5, preceding Eq.(26): the infinite Poisson photon-number law.
Nonnegative intensity and normalization are concluded below, not assumed. -/
def poissonPhotonLaw (intensity : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-intensity) * intensity ^ n / (Nat.factorial n : ℝ)

/-- PDF p.5, Eq.(25): total intensity after interference, including the
noninterfering portion. delta is the output displacement, possibly complex. -/
def mismatchIntensity (alpha tau xi : ℝ) (delta : ℂ) (plus : Bool) : ℝ :=
  (1 - xi) * (tau * alpha ^ 2 + Complex.normSq delta) +
    xi * Complex.normSq
      ((Real.sqrt tau : ℂ) * signalAmplitude alpha plus + delta)

/-- PDF pp.5--6, Eqs.(25)--(26): physical Poisson laws and the same fixed
on/off decoding. No optimized displacement or error formula is assumed. -/
def imperfectError (alpha eta nu tau xi : ℝ) (delta : ℂ) : ℝ :=
  (countNoClick eta nu (poissonPhotonLaw (mismatchIntensity alpha tau xi delta true)) +
    1 - countNoClick eta nu
      (poissonPhotonLaw (mismatchIntensity alpha tau xi delta false))) / 2

/-- PDF p.5: finite-beamsplitter local oscillator for output displacement delta.
Used only for tau<1. tau=1 is the ideal displacement limit, not this division. -/
def localOscillator (tau : ℝ) (delta : ℂ) : ℂ :=
  delta / (Real.sqrt (1 - tau) : ℂ)

example : signalAmplitude 0 true = signalAmplitude 0 false := by
  simp [signalAmplitude]

example : photonLaw (fockKet 0) 0 = 1 := by
  simp [photonLaw, fockKet, lp.single_apply]

example (eta nu : ℝ) :
    countNoClick eta nu (fun n : ℕ => if n = 0 then 1 else 0) = Real.exp (-nu) := by
  simp [countNoClick]

example : coherentCoefficient 0 0 = 1 := by
  norm_num [coherentCoefficient]

example : poissonPhotonLaw 0 0 = 1 := by
  norm_num [poissonPhotonLaw]

example (n : ℕ) : poissonPhotonLaw 0 (n + 1) = 0 := by
  simp [poissonPhotonLaw]

example : IsGaussianUnitary (LinearIsometryEquiv.refl ℂ Fock) := by
  refine ⟨LinearMap.id, ?_, 0, ?_⟩
  · intro z w
    rfl
  · intro z psi
    simp

example (alpha : ℝ) (delta : ℂ) (plus : Bool) :
    mismatchIntensity alpha 1 1 delta plus =
      Complex.normSq (signalAmplitude alpha plus + delta) := by
  simp [mismatchIntensity]

example (delta : ℂ) : localOscillator 0 delta = delta := by
  simp [localOscillator]

example (eta nu : ℝ) (preprocess : Fock → Fock) :
    receiverError 0 eta nu preprocess = 1 / 2 := by
  simp [receiverError, signalAmplitude] <;> ring

end QAlgorithms.Papers.Independent.Intake100.P08


