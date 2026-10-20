-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P04
-- name    : QAlgorithms_Papers_Independent_Frontier18_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:49:58.745981+00:00
-- url     : https://prove2.me/theorems/6284fa8a-e53b-498b-8460-734bc858c6f0
-- title:
--   Definitions for Multiple-Access Bosonic Communications
-- statement:
--   The objects the formalized statements of *Multiple-Access Bosonic Communications* (arXiv:quant-ph/0506171) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GaussianCode`: PDF p.2: a block code for m independent senders, d measured real quadratures, and n channel uses (or n positive-frequency modes in a wideband code). Each encoder sees only its own message. A decoder processes the entire measured block.
--   - `blockNoise`: PDF p.2: independent Gaussian noises across uses and quadratures, each of variance v. Homodyne uses d=1,v=1/4; heterodyne uses d=2,v=1/2.
--   - `measuredOutput`: PDF p.2: the measured beam-splitter signal plus classical noise. For heterodyne, the two coordinates are the real and imaginary parts of the amplitude.
--   - `measuredBlockError`: PDF p.2: average probability that at least one message is decoded incorrectly. The finite product of uniform messages is independent of the Gaussian noise. All Gaussian laws here are probability measures, so toReal never discards infinite mass. This is the classical measured Gaussian channel error, not the accepted finite-dimensional quantum `Information100.P63.averageError`, whose arguments are a superoperator and POVM code.
--   - `inputCost`: PDF pp.2–3,(14),(15): average transmitted cost, with an explicit per-mode weight. Single-mode weight is 1/n; wideband weight is hbar*omega/T. This averages over the sender's own uniform message, rather than taking a peak constraint.
--   - `GaussianAchievable`: PDF p.2: operational achievability with fixed quadrature measurement, mean photon budgets nbar, and arbitrarily small average error along arbitrarily long blocks. Rates are natural logarithms of message counts per channel use.
--   - `gaussianCapacity`: PDF p.2: the closed operational region, defined from codes and errors. No Gaussian capacity formula or Holevo expression is inserted into this definition.
--   - `homodyneCapacity`: PDF p.2,(5),(7): homodyne, one real quadrature, vacuum-noise variance 1/4.
--   - `heterodyneCapacity`: PDF p.2,(6),(8): heterodyne, two real quadratures, variance 1/2 in each.
--   - `modeFrequency`: PDF p.3,(13): mode t represents frequency 2*pi*(t+1)/T; there is no DC mode.
--   - `WidebandAchievable`: PDF pp.3–4,(13)–(15),(21): long-duration wideband achievability. A code may use any finite number K of positive-frequency modes, with no bandwidth cutoff uniform in T. All modes are independent. The weight hbar*omega/T equals hbar*omega*Delta/(2*pi). Rates are per unit time, not per mode. The closure below includes limits of codes with growing frequency support.
--   - `widebandCapacity`: PDF pp.3–4: closed operational wideband region for the specified measured channel.
--   - `homodyneSpectrum`: PDF p.4,(17)–(19): received homodyne water-filling spectrum of received power q. Zero outside the positive-frequency cutoff is explicit, including q=0. This normalization is for homodyne only.
--   - `spectrumPower`: PDF p.3,(14),(15), continuum limit: received power of a photon-number spectrum.
--   - `homodyneSpectrumRate`: PDF pp.3–4: continuum homodyne information integral, in nats per unit time.
--   - `helperSqueeze`: PDF p.10,(81): Bob expends all nB photons on squeezing, Z=asinh(sqrt nB). The logarithmic expression avoids a choice of inverse-hyperbolic notation.
--   - `helperNoise`: PDF p.10,(81): measured output variance for Alice squeeze z and Bob helper squeeze Z. The theorem checks strict positivity before constructing the noise law.
--   - `helperCapacity`: PDF p.10,(81): the actual homodyne channel with a zero-message squeezed helper. The one real input is Alice's displacement, with remaining budget nA-sinh(z)^2. The fixed Gaussian squeezed seeds produce exactly helperNoise, independently on all uses. Bob has one message; his seed energy is nB. No quantum receiver is used.
--   - `helperRate`: PDF p.10,(81): the displayed achievable information rate, not a capacity definition. Only 0<eta<=1, nonnegative budgets, and feasible squeezing are used below.
--   - `selectedSqueeze`: PDF p.10,(82): the selected squeeze for the ordered limiting argument. This is not declared optimal for a finite helper budget.
--   - `heterodyneSums`: PDF p.9,(6c),(80): sums attained in the operational heterodyne region. The associated theorem states IsGreatest, avoiding an empty/unbounded supremum default.
-- source:
--   Multiple-Access Bosonic Communications, arXiv:quant-ph/0506171v2, https://arxiv.org/abs/quant-ph/0506171v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49

/-!
# Multiple-Access Bosonic Communications

Statements from arXiv:quant-ph/0506171v2. The measured channels are represented
by their exact real Gaussian input/output laws (PDF p.2 and p.10). Codes below
have independent, uniformly distributed messages, separate deterministic encoders,
no shared randomness or entanglement, and an arbitrary measurable classical decoder.
The quantum collective-receiver nodes are explicitly deferred in HARD.md;
no capacity is defined by a proposed closed-form answer.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace QAlgorithms.Papers.Independent.Frontier18.P04

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- PDF p.2: a block code for m independent senders, d measured real quadratures,
and n channel uses (or n positive-frequency modes in a wideband code).
Each encoder sees only its own message. A decoder processes the entire measured block. -/
structure GaussianCode (m d n : ℕ) where
  messages : Fin m → ℕ
  messagesPositive : ∀ i, 0 < messages i
  encode : (i : Fin m) → Fin (messages i) → Fin n → Fin d → ℝ
  decode : (Fin n → Fin d → ℝ) → ((i : Fin m) → Fin (messages i))
  measurableDecode : Measurable decode

/-- PDF p.2: independent Gaussian noises across uses and quadratures, each of
variance v. Homodyne uses d=1,v=1/4; heterodyne uses d=2,v=1/2. -/
def blockNoise (d n : ℕ) (v : ℝ≥0) : Measure (Fin n → Fin d → ℝ) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin d => gaussianReal 0 v))

/-- PDF p.2: the measured beam-splitter signal plus classical noise.
For heterodyne, the two coordinates are the real and imaginary parts of the amplitude. -/
def measuredOutput {m d n : ℕ} (c : GaussianCode m d n)
    (eta : Fin m → ℝ) (message : (i : Fin m) → Fin (c.messages i))
    (noise : Fin n → Fin d → ℝ) : Fin n → Fin d → ℝ :=
  fun t q => (∑ i, Real.sqrt (eta i) * c.encode i (message i) t q) + noise t q

/-- PDF p.2: average probability that at least one message is decoded incorrectly.
The finite product of uniform messages is independent of the Gaussian noise.
All Gaussian laws here are probability measures, so toReal never discards infinite mass.
This is the classical measured Gaussian channel error, not the accepted finite-dimensional
quantum `Information100.P63.averageError`, whose arguments are a superoperator and POVM code. -/
def measuredBlockError {m d n : ℕ} (c : GaussianCode m d n)
    (v : ℝ≥0) (eta : Fin m → ℝ) : ℝ :=
  (∑ message : ((i : Fin m) → Fin (c.messages i)),
    ((blockNoise d n v) {z | c.decode (measuredOutput c eta message z) ≠ message}).toReal) /
      (∏ i, (c.messages i : ℝ))

/-- PDF pp.2–3,(14),(15): average transmitted cost, with an explicit per-mode
weight. Single-mode weight is 1/n; wideband weight is hbar*omega/T.
This averages over the sender's own uniform message, rather than taking a peak constraint. -/
def inputCost {m d n : ℕ} (c : GaussianCode m d n)
    (weight : Fin n → ℝ) (i : Fin m) : ℝ :=
  (∑ message : Fin (c.messages i), ∑ t, weight t * ∑ q, (c.encode i message t q) ^ 2) /
    (c.messages i : ℝ)

/-- PDF p.2: operational achievability with fixed quadrature measurement, mean
photon budgets nbar, and arbitrarily small average error along arbitrarily long blocks.
Rates are natural logarithms of message counts per channel use. -/
def GaussianAchievable {m : ℕ} (d : ℕ) (v : ℝ≥0)
    (eta nbar R : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ R i) ∧ ∀ epsilon : ℝ, 0 < epsilon → ∀ n0 : ℕ,
    ∃ n : ℕ, 0 < n ∧ n0 ≤ n ∧ ∃ c : GaussianCode m d n,
      (∀ i, inputCost c (fun _ => 1 / (n : ℝ)) i ≤ nbar i) ∧
      measuredBlockError c v eta ≤ epsilon ∧
      ∀ i, R i - epsilon ≤ Real.log (c.messages i : ℝ) / (n : ℝ)

/-- PDF p.2: the closed operational region, defined from codes and errors.
No Gaussian capacity formula or Holevo expression is inserted into this definition. -/
def gaussianCapacity {m : ℕ} (d : ℕ) (v : ℝ≥0)
    (eta nbar : Fin m → ℝ) : Set (Fin m → ℝ) :=
  closure {R | GaussianAchievable d v eta nbar R}

/-- PDF p.2,(5),(7): homodyne, one real quadrature, vacuum-noise variance 1/4. -/
def homodyneCapacity {m : ℕ} (eta nbar : Fin m → ℝ) : Set (Fin m → ℝ) :=
  gaussianCapacity 1 (1 / 4) eta nbar

/-- PDF p.2,(6),(8): heterodyne, two real quadratures, variance 1/2 in each. -/
def heterodyneCapacity {m : ℕ} (eta nbar : Fin m → ℝ) : Set (Fin m → ℝ) :=
  gaussianCapacity 2 (1 / 2) eta nbar

/-- PDF p.3,(13): mode t represents frequency 2*pi*(t+1)/T; there is no DC mode. -/
def modeFrequency (T : ℝ) {K : ℕ} (t : Fin K) : ℝ :=
  2 * Real.pi * ((t.val : ℝ) + 1) / T

/-- PDF pp.3–4,(13)–(15),(21): long-duration wideband achievability.
A code may use any finite number K of positive-frequency modes, with no bandwidth
cutoff uniform in T. All modes are independent. The weight hbar*omega/T equals
hbar*omega*Delta/(2*pi). Rates are per unit time, not per mode.
The closure below includes limits of codes with growing frequency support. -/
def WidebandAchievable {m : ℕ} (d : ℕ) (v : ℝ≥0)
    (hbar : ℝ) (eta power R : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ R i) ∧ ∀ epsilon : ℝ, 0 < epsilon → ∀ T0 : ℝ,
    ∃ T : ℝ, 0 < T ∧ T0 ≤ T ∧ ∃ K : ℕ, 0 < K ∧
    ∃ c : GaussianCode m d K,
      (∀ i, inputCost c (fun t => hbar * modeFrequency T t / T) i ≤ power i) ∧
      measuredBlockError c v eta ≤ epsilon ∧
      ∀ i, R i - epsilon ≤ Real.log (c.messages i : ℝ) / T

/-- PDF pp.3–4: closed operational wideband region for the specified measured channel. -/
def widebandCapacity {m : ℕ} (d : ℕ) (v : ℝ≥0)
    (hbar : ℝ) (eta power : Fin m → ℝ) : Set (Fin m → ℝ) :=
  closure {R | WidebandAchievable d v hbar eta power R}

/-- PDF p.4,(17)–(19): received homodyne water-filling spectrum of received power q.
Zero outside the positive-frequency cutoff is explicit, including q=0.
This normalization is for homodyne only. -/
def homodyneSpectrum (hbar q omega : ℝ) : ℝ :=
  if 0 < omega ∧ omega ≤ 4 * Real.sqrt (Real.pi * q / hbar) then
    Real.sqrt (Real.pi * q / hbar) / omega - 1 / 4 else 0

/-- PDF p.3,(14),(15), continuum limit: received power of a photon-number spectrum. -/
def spectrumPower (hbar : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ omega in Set.Ioi (0 : ℝ), hbar * omega * f omega / (2 * Real.pi)

/-- PDF pp.3–4: continuum homodyne information integral, in nats per unit time. -/
def homodyneSpectrumRate (f : ℝ → ℝ) : ℝ :=
  ∫ omega in Set.Ioi (0 : ℝ), Real.log (1 + 4 * f omega) / (4 * Real.pi)

/-- PDF p.10,(81): Bob expends all nB photons on squeezing, Z=asinh(sqrt nB).
The logarithmic expression avoids a choice of inverse-hyperbolic notation. -/
def helperSqueeze (nB : ℝ) : ℝ :=
  Real.log (Real.sqrt nB + Real.sqrt (nB + 1))

/-- PDF p.10,(81): measured output variance for Alice squeeze z and Bob helper
squeeze Z. The theorem checks strict positivity before constructing the noise law. -/
def helperNoise (eta nB z : ℝ) : ℝ :=
  (eta * Real.exp (-2 * z) + (1 - eta) * Real.exp (-2 * helperSqueeze nB)) / 4

/-- PDF p.10,(81): the actual homodyne channel with a zero-message squeezed helper.
The one real input is Alice's displacement, with remaining budget nA-sinh(z)^2.
The fixed Gaussian squeezed seeds produce exactly helperNoise, independently on
all uses. Bob has one message; his seed energy is nB. No quantum receiver is used. -/
def helperCapacity (eta nA nB z : ℝ) : Set (Fin 1 → ℝ) :=
  gaussianCapacity 1 (Real.toNNReal (helperNoise eta nB z))
    (fun _ => eta) (fun _ => nA - (Real.sinh z) ^ 2)

/-- PDF p.10,(81): the displayed achievable information rate, not a capacity definition.
Only 0<eta<=1, nonnegative budgets, and feasible squeezing are used below. -/
def helperRate (eta nA nB z : ℝ) : ℝ :=
  (1 / 2) * Real.log (1 + 4 * (nA - (Real.sinh z) ^ 2) /
    (Real.exp (-2 * z) + (1 - eta) * Real.exp (-2 * helperSqueeze nB) / eta))

/-- PDF p.10,(82): the selected squeeze for the ordered limiting argument.
This is not declared optimal for a finite helper budget. -/
def selectedSqueeze (nA : ℝ) : ℝ := Real.log (2 * nA + 1) / 2

/-- PDF p.9,(6c),(80): sums attained in the operational heterodyne region.
The associated theorem states IsGreatest, avoiding an empty/unbounded supremum default. -/
def heterodyneSums (eta nA nB : ℝ) : Set ℝ :=
  {s | ∃ R ∈ heterodyneCapacity (![eta, 1 - eta] : Fin 2 → ℝ)
      (![nA, nB] : Fin 2 → ℝ), s = R 0 + R 1}

example : thermalEntropy 0 = 0 := by simp [thermalEntropy]

example {m d n : ℕ} (c : GaussianCode m d n)
    (eta : Fin m → ℝ) (message : (i : Fin m) → Fin (c.messages i)) :
    measuredOutput c eta message 0 =
      fun t q => ∑ i, Real.sqrt (eta i) * c.encode i (message i) t q := by
  funext t q
  simp [measuredOutput]

example {m d n : ℕ} (c : GaussianCode m d n) (i : Fin m) :
    inputCost c (fun _ => 0) i = 0 := by simp [inputCost]

example (hbar q : ℝ) : homodyneSpectrum hbar q 0 = 0 := by
  simp [homodyneSpectrum]

example (hbar omega : ℝ) (homega : 0 < omega) :
    homodyneSpectrum hbar 0 omega = 0 := by
  simp [homodyneSpectrum, not_le.mpr homega]

example : helperSqueeze 0 = 0 := by simp [helperSqueeze]

example (eta nB : ℝ) : helperRate eta 0 nB 0 = 0 := by
  simp [helperRate]

end QAlgorithms.Papers.Independent.Frontier18.P04


