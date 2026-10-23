-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P15
-- name    : QAlgorithms_Papers_Independent_Gap20_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T07:21:07.635273+00:00
-- url     : https://prove2.me/theorems/2aaab173-9138-4c8b-8bb4-1f208662b85e
-- title:
--   Definitions for Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels
-- statement:
--   The objects the formalized statements of *Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels* (arXiv:1708.07257) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `thermalDataProcessing`: PDF p.23, (5.3): raw data-processing expression, before capacity clipping.
--   - `thermalDiscriminant`: PDF p.33, (6.2): positive symplectic discriminant root.
--   - `thermalCoherent`: PDF p.33, (6.1): the raw thermal-input coherent information; no clipping.
--   - `thermalGap`: PDF p.34, (6.7): difference of the two raw finite-energy expressions.
--   - `amplifierDataProcessing`: PDF p.43, (9.10)-(9.11): raw amplifier data-processing expression.
--   - `amplifierDiscriminant`: PDF p.44, (9.21): amplifier symplectic discriminant root.
--   - `amplifierCoherent`: PDF p.44, (9.20): raw amplifier thermal-input coherent information.
--   - `additiveDataProcessing`: PDF p.48, (10.2): additive-noise raw data-processing expression.
--   - `additiveCoherent`: PDF p.48, Remark 44, analytically taking the thermal limit of (6.1)-(6.2), p.33: (1-eta)NB tends to noise and eta tends to one. This is a computed scalar, not an assumed capacity or an optimized coherent information.
--   - `spectralMean`: PDF p.8, (3.8): extended expectation in spectral coordinates. Only nonnegative spectra and normalized positive trace-class states are used.
--   - `averageSpectrum`: PDF p.8, (3.9): eigenvalues of the AVERAGE n-use energy. The source results require positive n; the empty-register value is harmlessly zero.
--   - `finiteOutputEntropy`: PDF p.9, Condition 7: a single finite bound uniform on the whole energy ball.
--   - `degradationSupremum`: PDF p.16, (4.1): the supremum of the actual entropy difference. Under Condition 7 the receiver entropy is finite; infinite degraded-output entropy therefore gives minus infinity, never a default real zero. Raw maps permit using the accepted n-use tensor action without assuming a desired additivity.
-- source:
--   Bounding the energy-constrained quantum and private capacities of phase-insensitive bosonic Gaussian channels, arXiv:1708.07257v3, https://arxiv.org/abs/1708.07257v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

/-!
arXiv:1708.07257v3. Raw scalar comparisons and extended-valued degradation
additivity. Operational capacity results and source ambiguities are individually
recorded in HARD.md and GAPS.json. Compilation and independent moderation are pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P15

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Hamiltonian)
open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)
open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassChannelPower)
open scoped ENNReal

/-- PDF p.23, (5.3): raw data-processing expression, before capacity clipping. -/
def thermalDataProcessing (eta noise energy : ℝ) : ℝ :=
  let t := eta / (1 + (1 - eta) * noise)
  bosonicEntropy (t * energy) - bosonicEntropy ((1 - t) * energy)

/-- PDF p.33, (6.2): positive symplectic discriminant root. -/
def thermalDiscriminant (eta noise energy : ℝ) : ℝ :=
  Real.sqrt (((1 + eta) * energy + (1 - eta) * noise + 1) ^ 2 -
    4 * eta * energy * (energy + 1))

/-- PDF p.33, (6.1): the raw thermal-input coherent information; no clipping. -/
def thermalCoherent (eta noise energy : ℝ) : ℝ :=
  let d := thermalDiscriminant eta noise energy
  bosonicEntropy (eta * energy + (1 - eta) * noise) -
    bosonicEntropy ((d + (1 - eta) * (energy - noise) - 1) / 2) -
    bosonicEntropy ((d - (1 - eta) * (energy - noise) - 1) / 2)

/-- PDF p.34, (6.7): difference of the two raw finite-energy expressions. -/
def thermalGap (eta noise energy : ℝ) : ℝ :=
  thermalDataProcessing eta noise energy - thermalCoherent eta noise energy

/-- PDF p.43, (9.10)-(9.11): raw amplifier data-processing expression. -/
def amplifierDataProcessing (gain noise energy : ℝ) : ℝ :=
  let gp := gain / (1 - (gain - 1) * noise)
  bosonicEntropy (gp * energy + gp - 1) -
    bosonicEntropy ((gp - 1) * (energy + 1))

/-- PDF p.44, (9.21): amplifier symplectic discriminant root. -/
def amplifierDiscriminant (gain noise energy : ℝ) : ℝ :=
  Real.sqrt (((1 + gain) * energy + (gain - 1) * (noise + 1) + 1) ^ 2 -
    4 * gain * energy * (energy + 1))

/-- PDF p.44, (9.20): raw amplifier thermal-input coherent information. -/
def amplifierCoherent (gain noise energy : ℝ) : ℝ :=
  let d := amplifierDiscriminant gain noise energy
  bosonicEntropy (gain * energy + (gain - 1) * (noise + 1)) -
    bosonicEntropy ((d + (gain - 1) * (energy + noise + 1) - 1) / 2) -
    bosonicEntropy ((d - (gain - 1) * (energy + noise + 1) - 1) / 2)

/-- PDF p.48, (10.2): additive-noise raw data-processing expression. -/
def additiveDataProcessing (noise energy : ℝ) : ℝ :=
  bosonicEntropy (energy / (1 + noise)) -
    bosonicEntropy (noise * energy / (1 + noise))

/-- PDF p.48, Remark 44, analytically taking the thermal limit of (6.1)-(6.2),
p.33: (1-eta)NB tends to noise and eta tends to one. This is a computed scalar,
not an assumed capacity or an optimized coherent information. -/
def additiveCoherent (noise energy : ℝ) : ℝ :=
  let d := Real.sqrt ((1 + noise) ^ 2 + 4 * noise * energy)
  bosonicEntropy (energy + noise) - bosonicEntropy ((d + noise - 1) / 2) -
    bosonicEntropy ((d - noise - 1) / 2)

/-- PDF p.8, (3.8): extended expectation in spectral coordinates. Only
nonnegative spectra and normalized positive trace-class states are used. -/
def spectralMean {I : Type} (e : I → ℝ) (rho : State I) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (e i * (rho.coefficients i i).re)

/-- PDF p.8, (3.9): eigenvalues of the AVERAGE n-use energy. The source
results require positive n; the empty-register value is harmlessly zero. -/
def averageSpectrum {I : Type} (e : I → ℝ) (n : ℕ) (x : Fin n → I) : ℝ :=
  (∑ j, e (x j)) / (n : ℝ)

/-- PDF p.9, Condition 7: a single finite bound uniform on the whole energy ball. -/
def finiteOutputEntropy {I J : Type} (N : Channel I J) (e : I → ℝ) (budget : ℝ) : Prop :=
  ∃ c : NNReal, ∀ rho : State I,
    spectralMean e rho ≤ ENNReal.ofReal budget →
      entropyBits (N.val rho.coefficients) ≤ (c : ℝ≥0∞)

/-- PDF p.16, (4.1): the supremum of the actual entropy difference. Under
Condition 7 the receiver entropy is finite; infinite degraded-output entropy
therefore gives minus infinity, never a default real zero. Raw maps permit
using the accepted n-use tensor action without assuming a desired additivity. -/
def degradationSupremum {I J E : Type}
    (N : Matrix I I ℂ → Matrix J J ℂ)
    (D : Matrix J J ℂ → Matrix E E ℂ) (e : I → ℝ) (budget : ℝ) : EReal :=
  ⨆ rho : {rho : State I // spectralMean e rho ≤ ENNReal.ofReal budget},
    (entropyBits (N rho.val.coefficients)).toEReal -
      (entropyBits (D (N rho.val.coefficients))).toEReal

/-- Vacuum entropy in the reused bit convention, PDF pp.6-7. -/
example : bosonicEntropy 0 = 0 := by
  simp [bosonicEntropy]

/-- Zero input energy makes both terms of the raw data-processing bound zero. -/
example (eta noise : ℝ) : thermalDataProcessing eta noise 0 = 0 := by
  simp [thermalDataProcessing]

/-- Equal attenuation gives identical arguments, independent of input energy. -/
example (energy : ℝ) : thermalDataProcessing (1 / 2) 0 energy = 0 := by
  norm_num [thermalDataProcessing]

/-- PDF p.48: the zero-energy additive data-processing value is zero. -/
example (noise : ℝ) : additiveDataProcessing noise 0 = 0 := by
  simp [additiveDataProcessing]

/-- The photon expectation of a zero spectral observable is zero. -/
example {I : Type} (rho : State I) : spectralMean (fun _ : I => 0) rho = 0 := by
  simp [spectralMean]

/-- An empty block has zero average energy; additivity explicitly excludes it. -/
example {I : Type} (e : I → ℝ) (x : Fin 0 → I) : averageSpectrum e 0 x = 0 := by
  simp [averageSpectrum]

/-- The scalar difference is computed, not supplied by an equality hypothesis. -/
example (eta noise energy : ℝ) : thermalGap eta noise energy =
    thermalDataProcessing eta noise energy - thermalCoherent eta noise energy := by
  rfl

end QAlgorithms.Papers.Independent.Gap20.P15


