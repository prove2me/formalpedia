-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P02
-- name    : QAlgorithms_Papers_Independent_Frontier18_P02
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:47:26.81026+00:00
-- url     : https://prove2.me/theorems/61688e0c-dd59-42ad-91ea-50030986bfbb
-- title:
--   Definitions for Capacities of Quantum Amplifier Channels
-- statement:
--   The objects the formalized statements of *Capacities of Quantum Amplifier Channels* (arXiv:1605.04922) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `detectionDimensions`: PDF p.11, Appendix B: one real quadrature for homodyne (`false`), two for heterodyne (`true`).
--   - `detectionXi`: PDF pp.8,11, (66), (B7)--(B10): the detection prefactor xi.
--   - `detectionNoiseVariance`: PDF p.11, (B3)--(B6): component noise variance. For physical gain >= 1 this is (xi + gain - 1)/2, strictly positive. The max only extends the parameterization to unphysical gains, which are excluded in the theorem.
--   - `DetectionBlock`: PDF p.11, Appendix B: n measured symbols, with the specified real quadrature count. This space contains all real classical codewords.
--   - `detectionLaw`: PDF p.11, (B3)--(B6): independent additive Gaussian noise at every use and quadrature. `signalGain` is gain for Bob and gain-1 for Charlie. For heterodyne Charlie, the fixed conjugation of the imaginary quadrature is undone locally; the circular Gaussian noise law is unchanged. Only receiver marginals are needed for independent local decoding errors.
--   - `DetectionCode`: PDF pp.8,11, Section IV.C and Appendix B: a classical Gaussian broadcast code with independent uniform messages, arbitrary joint codewords and separate measurable decoders. No Gaussian distribution is imposed on the codebook. Message sets are positive; block length is positive in achievability below.
--   - `DetectionCode.HasEnergy`: PDF pp.3,5,11: unconditional average input power at each use, summed over the measured quadratures. Heterodyne has total power NS across both quadratures; homodyne uses the single encoded quadrature.
--   - `DetectionCode.bobError`: PDF pp.8,11: Bob's actual average message error under the induced classical channel. Probability measures have finite mass, so toReal does not turn an infinite measure into zero.
--   - `DetectionCode.charlieError`: PDF pp.8,11: Charlie's local average error; signal intensity gain is exactly gain-1, including the constant-output endpoint gain=1.
--   - `detectionCapacityRegion`: PDF pp.8,11, (66) and Appendix B: operational capacity of the induced classical Gaussian channel, defined independently of its rate formula. Arbitrarily small local error and rate slack are achieved at every sufficiently large positive block length, using codes obeying the per-use mean budget. Rates are bits per use. No unrestricted quantum capacity is defined here.
--   - `detectionRateRegion`: PDF p.8, (66), and p.11, (B9)--(B10): explicit rate region with ONE common power-sharing parameter. This is a formula, not the definition of operational capacity.
--   - `broadcastBobBoundary`: PDF p.6, (40): Bob's explicit achievable-region boundary. This scalar function makes no operational optimality assertion for noisy amplifiers.
--   - `broadcastCharlieBoundary`: PDF p.6, (41): Charlie's explicit achievable-region boundary, for the actual C output of (36), not a purified-environment complement.
-- source:
--   Capacities of Quantum Amplifier Channels, arXiv:1605.04922v3, https://arxiv.org/abs/1605.04922v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

/-!
# Capacities of Quantum Amplifier Channels

Qi--Wilde, arXiv:1605.04922v3. New statements cover Theorem 8, the induced
classical Gaussian coherent-detection channel, and the explicit large-gain
boundary limits. Operational quantum-capacity results requiring additional
infinite-dimensional channel and code interfaces are explicitly deferred.
The accepted high-energy scalar limit is reused by metadata, without duplication.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P02

open Filter MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.11, Appendix B: one real quadrature for homodyne (`false`),
two for heterodyne (`true`). -/
def detectionDimensions (heterodyne : Bool) : ℕ :=
  if heterodyne then 2 else 1

/-- PDF pp.8,11, (66), (B7)--(B10): the detection prefactor xi. -/
def detectionXi (heterodyne : Bool) : ℝ :=
  if heterodyne then 1 else 1 / 2

/-- PDF p.11, (B3)--(B6): component noise variance. For physical gain >= 1
this is (xi + gain - 1)/2, strictly positive. The max only extends the
parameterization to unphysical gains, which are excluded in the theorem. -/
def detectionNoiseVariance (heterodyne : Bool) (gain : ℝ) : NNReal :=
  ⟨max 0 ((detectionXi heterodyne + gain - 1) / 2), le_max_left _ _⟩

/-- PDF p.11, Appendix B: n measured symbols, with the specified real
quadrature count. This space contains all real classical codewords. -/
abbrev DetectionBlock (heterodyne : Bool) (n : ℕ) :=
  (Fin n × Fin (detectionDimensions heterodyne)) → ℝ

/-- PDF p.11, (B3)--(B6): independent additive Gaussian noise at every use
and quadrature. `signalGain` is gain for Bob and gain-1 for Charlie.
For heterodyne Charlie, the fixed conjugation of the imaginary quadrature
is undone locally; the circular Gaussian noise law is unchanged. Only
receiver marginals are needed for independent local decoding errors. -/
def detectionLaw (heterodyne : Bool) (n : ℕ) (gain signalGain : ℝ)
    (signal : DetectionBlock heterodyne n) : Measure (DetectionBlock heterodyne n) :=
  Measure.pi (fun j => ProbabilityTheory.gaussianReal
    (Real.sqrt signalGain * signal j) (detectionNoiseVariance heterodyne gain))

/-- PDF pp.8,11, Section IV.C and Appendix B: a classical Gaussian broadcast
code with independent uniform messages, arbitrary joint codewords and separate
measurable decoders. No Gaussian distribution is imposed on the codebook.
Message sets are positive; block length is positive in achievability below. -/
structure DetectionCode (heterodyne : Bool) (n : ℕ) where
  bobMessages : ℕ
  charlieMessages : ℕ
  bobMessages_pos : 0 < bobMessages
  charlieMessages_pos : 0 < charlieMessages
  encode : Fin bobMessages → Fin charlieMessages → DetectionBlock heterodyne n
  decodeBob : DetectionBlock heterodyne n → Fin bobMessages
  decodeCharlie : DetectionBlock heterodyne n → Fin charlieMessages
  decodeBob_measurable : Measurable decodeBob
  decodeCharlie_measurable : Measurable decodeCharlie

/-- PDF pp.3,5,11: unconditional average input power at each use, summed
over the measured quadratures. Heterodyne has total power NS across both
quadratures; homodyne uses the single encoded quadrature. -/
def DetectionCode.HasEnergy {heterodyne : Bool} {n : ℕ}
    (code : DetectionCode heterodyne n) (budget : ℝ) : Prop :=
  ∀ j : Fin n,
    (∑ b : Fin code.bobMessages, ∑ c : Fin code.charlieMessages,
      ∑ a : Fin (detectionDimensions heterodyne), code.encode b c (j, a) ^ 2) /
        ((code.bobMessages : ℝ) * (code.charlieMessages : ℝ)) ≤ budget

/-- PDF pp.8,11: Bob's actual average message error under the induced
classical channel. Probability measures have finite mass, so toReal does
not turn an infinite measure into zero. -/
def DetectionCode.bobError {heterodyne : Bool} {n : ℕ}
    (code : DetectionCode heterodyne n) (gain : ℝ) : ℝ :=
  (∑ b : Fin code.bobMessages, ∑ c : Fin code.charlieMessages,
    (detectionLaw heterodyne n gain gain (code.encode b c)
      {z | code.decodeBob z ≠ b}).toReal) /
        ((code.bobMessages : ℝ) * (code.charlieMessages : ℝ))

/-- PDF pp.8,11: Charlie's local average error; signal intensity gain is
exactly gain-1, including the constant-output endpoint gain=1. -/
def DetectionCode.charlieError {heterodyne : Bool} {n : ℕ}
    (code : DetectionCode heterodyne n) (gain : ℝ) : ℝ :=
  (∑ b : Fin code.bobMessages, ∑ c : Fin code.charlieMessages,
    (detectionLaw heterodyne n gain (gain - 1) (code.encode b c)
      {z | code.decodeCharlie z ≠ c}).toReal) /
        ((code.bobMessages : ℝ) * (code.charlieMessages : ℝ))

/-- PDF pp.8,11, (66) and Appendix B: operational capacity of the induced
classical Gaussian channel, defined independently of its rate formula.
Arbitrarily small local error and rate slack are achieved at every sufficiently
large positive block length, using codes obeying the per-use mean budget.
Rates are bits per use. No unrestricted quantum capacity is defined here. -/
def detectionCapacityRegion (heterodyne : Bool) (gain budget : ℝ) : Set (ℝ × ℝ) :=
  {rates | 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ delta : ℝ, 0 < delta →
      ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
        ∃ code : DetectionCode heterodyne n,
          code.HasEnergy budget ∧ code.bobError gain ≤ epsilon ∧
          code.charlieError gain ≤ epsilon ∧
          rates.1 - delta ≤ Real.logb 2 (code.bobMessages : ℝ) / (n : ℝ) ∧
          rates.2 - delta ≤ Real.logb 2 (code.charlieMessages : ℝ) / (n : ℝ)}

/-- PDF p.8, (66), and p.11, (B9)--(B10): explicit rate region with ONE
common power-sharing parameter. This is a formula, not the definition of
operational capacity. -/
def detectionRateRegion (heterodyne : Bool) (gain budget : ℝ) : Set (ℝ × ℝ) :=
  {rates | 0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧
    ∃ lambda : ℝ, 0 ≤ lambda ∧ lambda ≤ 1 ∧
      rates.1 ≤ detectionXi heterodyne * Real.logb 2
        (1 + lambda * gain * budget /
          (detectionXi heterodyne * (detectionXi heterodyne + gain - 1))) ∧
      rates.2 ≤ detectionXi heterodyne * Real.logb 2
        (1 + (1 - lambda) * (gain - 1) * budget /
          (detectionXi heterodyne * (detectionXi heterodyne + gain - 1) +
            lambda * (gain - 1) * budget))}

/-- PDF p.6, (40): Bob's explicit achievable-region boundary. This scalar
function makes no operational optimality assertion for noisy amplifiers. -/
def broadcastBobBoundary (gain budget noise lambda : ℝ) : ℝ :=
  thermalEntropy (gain * lambda * budget + (gain - 1) * (noise + 1)) -
    thermalEntropy ((gain - 1) * (noise + 1))

/-- PDF p.6, (41): Charlie's explicit achievable-region boundary, for the
actual C output of (36), not a purified-environment complement. -/
def broadcastCharlieBoundary (gain budget noise lambda : ℝ) : ℝ :=
  thermalEntropy ((gain - 1) * (budget + 1) + gain * noise) -
    thermalEntropy ((gain - 1) * (lambda * budget + 1) + gain * noise)

/-- Sanity check: homodyne vacuum component noise is 1/4 (PDF p.11). -/
example : detectionNoiseVariance false 1 = (1 / 4 : NNReal) := by
  apply Subtype.ext
  norm_num [detectionNoiseVariance, detectionXi]

/-- Sanity check: heterodyne vacuum component noise is 1/2 (PDF p.11). -/
example : detectionNoiseVariance true 1 = (1 / 2 : NNReal) := by
  apply Subtype.ext
  norm_num [detectionNoiseVariance, detectionXi]

/-- Sanity check: both Gaussian output laws are normalized probability
measures, even at zero signal gain (PDF p.11). -/
example (heterodyne : Bool) (n : ℕ) (gain signalGain : ℝ)
    (signal : DetectionBlock heterodyne n) :
    IsProbabilityMeasure (detectionLaw heterodyne n gain signalGain signal) := by
  unfold detectionLaw
  infer_instance

/-- Sanity check: a one-message, zero-input code exists for every block
length and both detectors (PDF p.11, Appendix B). -/
example (heterodyne : Bool) (n : ℕ) : Nonempty (DetectionCode heterodyne n) := by
  exact ⟨{
    bobMessages := 1
    charlieMessages := 1
    bobMessages_pos := by decide
    charlieMessages_pos := by decide
    encode := fun _ _ _ => 0
    decodeBob := fun _ => 0
    decodeCharlie := fun _ => 0
    decodeBob_measurable := measurable_const
    decodeCharlie_measurable := measurable_const
  }⟩

/-- Sanity check: zero signal gain erases the input codeword, as at
Charlie's identity-gain endpoint (PDF pp.5,11). -/
example (heterodyne : Bool) (n : ℕ) (gain : ℝ)
    (signal : DetectionBlock heterodyne n) :
    detectionLaw heterodyne n gain 0 signal =
      detectionLaw heterodyne n gain 0 (fun _ => 0) := by
  simp [detectionLaw]

/-- Sanity check: at gain=1 Charlie's boundary is zero, for every sharing
parameter and noise value (PDF p.6, (41)). -/
example (budget noise lambda : ℝ) : broadcastCharlieBoundary 1 budget noise lambda = 0 := by
  simp [broadcastCharlieBoundary]

/-- Sanity check: with lambda=0 Bob's boundary is zero (PDF p.6, (40)). -/
example (gain budget noise : ℝ) : broadcastBobBoundary gain budget noise 0 = 0 := by
  simp [broadcastBobBoundary]

end QAlgorithms.Papers.Independent.Frontier18.P02


