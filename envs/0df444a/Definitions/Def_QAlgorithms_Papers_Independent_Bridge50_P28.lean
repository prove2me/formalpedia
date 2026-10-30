-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P28
-- name    : QAlgorithms_Papers_Independent_Bridge50_P28
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:25:52.587513+00:00
-- url     : https://prove2.me/theorems/ce27755e-7187-4ebd-a755-8260826265f4
-- title:
--   Definitions for The classical capacity of quantum thermal noise channels to within 1.45 bits
-- statement:
--   The objects the formalized statements of *The classical capacity of quantum thermal noise channels to within 1.45 bits* (arXiv:1207.0256) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `thermalNoiseChannelKernel`: PDF p.1: coefficient adapter for the accepted thermal beam-splitter channel. The environment has photon mean NE; lambda is intensity transmissivity. On trace class boundedOperator has its unique bounded realization.
--   - `quantumLimitedAmplifierKernel`: PDF p.2 and p.3 note [19]: accepted vacuum amplifier, intensity gain G. Its countable Kraus operators have amplitude parameter sqrt(G), including G=1. Trace-norm convergence is part of the accepted physical channel construction.
--   - `FiniteCollectivePOVM`: PDF p.1: finite-outcome collective decoding on a complete Hilbert space. Positive bounded effects sum to the identity. Finite additivity suffices for the finite message alphabet; there is no finite photon-number cutoff.
--   - `PhotonConstrainedClassicalCode`: PDF p.1: an unassisted n-use classical code, with positive n and M. Signals are arbitrary normalized mixed states, possibly entangled across uses. One decoder is fixed before the unknown message.
--   - `photonCodeAverageInput`: PDF p.1: uniform-message average block input. No per-message energy cap.
--   - `photonCodeSuccessProbability`: PDF p.1: uniform-message success using the actual memoryless channel. The trace-class/bounded pairing converges even for infinite-rank signal states.
--   - `codeWithinBudget`: PDF p.1: mean input energy only. The fixed input basis weight is summed across the block and averaged over messages; an infinite expectation stays infinity. For the oscillator the weight is the photon number j itself.
--   - `classicalPhotonRateAchievable`: PDF p.1: rates in bits/use with vanishing uniform-message average error. For each positive error and rate slack, all sufficiently large positive lengths admit one code satisfying the SAME average input budget. No feedback, shared entanglement, product-state restriction, or energy cap after the channel.
--   - `classicalPhotonCapacityBits`: PDF p.1: operational classical capacity as an extended nonnegative supremum. Empty rate sets give zero; unbounded sets give infinity. Neither g nor a scalar capacity bound appears in this definition.
--   - `coherentSignalRateBits`: PDF pp.1--2, Eq.(1) and Theorem 1: Holevo's coherent-signal rate in bits. The accepted g uses natural logarithms and 0 log 0=0.
--   - `thermalUpperBoundBits`: PDF p.2, Eq.(3): finite numerical upper bound, not a capacity definition.
--   - `thermalBoundGapNats`: PDF p.2, Lemma 1: the numerical upper-minus-lower gap in nats. Source limit and strict derivative claims use Y>0, and X>0 where stated.
-- source:
--   The classical capacity of quantum thermal noise channels to within 1.45 bits, arXiv:1207.0256v1, https://arxiv.org/abs/1207.0256v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

/-!
König--Smith, arXiv:1207.0256v1, PDF pp.1--3.
Full countable Fock spaces; arbitrary mixed and entangled block signals;
unassisted classical communication; uniform-message average error and mean block
photon energy. Capacity is an operational extended supremum, independently of g.
Only pinned accepted library modules are imported. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P28

open Filter
open scoped BigOperators NNReal ENNReal Topology
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)
open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassChannelPower tracePair)
open QAlgorithms.Papers.Independent.Gap48.P26 (weightedPhotonExpectation)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-! The accepted basenames `Support50.P11.codeAverageInput` and
`Dependency50.P23.codeSuccess` / `Dependency50.P45.codeSuccess` describe
finite-dimensional bipartite or assisted codes. Their Fintype requirements and
code types cannot represent this paper's full countable Fock inputs. The two
photon-code definitions below therefore have distinct names and retain the
required trace-class domain; they are not copies of those frozen objects. -/

/-- PDF p.1: coefficient adapter for the accepted thermal beam-splitter channel.
The environment has photon mean NE; lambda is intensity transmissivity.
On trace class boundedOperator has its unique bounded realization. -/
def thermalNoiseChannelKernel (lam NE : ℝ) (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  operatorCoeff (QAlgorithms.Papers.Independent.Claimed50.P39.thermal lam NE
    (boundedOperator X))

/-- PDF p.2 and p.3 note [19]: accepted vacuum amplifier, intensity gain G.
Its countable Kraus operators have amplitude parameter sqrt(G), including G=1.
Trace-norm convergence is part of the accepted physical channel construction. -/
def quantumLimitedAmplifierKernel (G : ℝ) (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  operatorCoeff (QAlgorithms.Papers.Independent.Claimed50.P39.amplifier G
    (boundedOperator X))

/-- PDF p.1: finite-outcome collective decoding on a complete Hilbert space.
Positive bounded effects sum to the identity. Finite additivity suffices for the
finite message alphabet; there is no finite photon-number cutoff. -/
structure FiniteCollectivePOVM (J : Type) (M : ℕ) where
  effect : Fin M → Hilbert J →L[ℂ] Hilbert J
  positive : ∀ m u, (inner (𝕜 := ℂ) u (effect m u)).im = 0 ∧
    0 ≤ (inner (𝕜 := ℂ) u (effect m u)).re
  total : (∑ m, effect m) = ContinuousLinearMap.id ℂ (Hilbert J)

/-- PDF p.1: an unassisted n-use classical code, with positive n and M.
Signals are arbitrary normalized mixed states, possibly entangled across uses.
One decoder is fixed before the unknown message. -/
structure PhotonConstrainedClassicalCode (I J : Type) (n : ℕ) where
  block_pos : 0 < n
  messages : ℕ
  messages_pos : 0 < messages
  signal : Fin messages → State (Fin n → I)
  decoder : FiniteCollectivePOVM (Fin n → J) messages

/-- PDF p.1: uniform-message average block input. No per-message energy cap. -/
def photonCodeAverageInput {I J : Type} {n : ℕ}
    (c : PhotonConstrainedClassicalCode I J n) : Matrix (Fin n → I) (Fin n → I) ℂ :=
  (1 / (c.messages : ℂ)) • ∑ m, (c.signal m).coefficients

/-- PDF p.1: uniform-message success using the actual memoryless channel.
The trace-class/bounded pairing converges even for infinite-rank signal states. -/
def photonCodeSuccessProbability {I J : Type} {n : ℕ}
    (T : Matrix I I ℂ → Matrix J J ℂ)
    (c : PhotonConstrainedClassicalCode I J n) : ℝ :=
  (∑ m, (tracePair (traceClassChannelPower T n (c.signal m).coefficients)
    (operatorCoeff (c.decoder.effect m))).re) / (c.messages : ℝ)

/-- PDF p.1: mean input energy only. The fixed input basis weight is summed
across the block and averaged over messages; an infinite expectation stays
infinity. For the oscillator the weight is the photon number j itself. -/
def codeWithinBudget {I J : Type} {n : ℕ} (weight : I → ℕ) (N : ℝ)
    (c : PhotonConstrainedClassicalCode I J n) : Prop :=
  weightedPhotonExpectation (fun a : Fin n → I => ∑ t, weight (a t))
    (photonCodeAverageInput c) ≤ ENNReal.ofReal ((n : ℝ) * N)

/-- PDF p.1: rates in bits/use with vanishing uniform-message average error.
For each positive error and rate slack, all sufficiently large positive lengths
admit one code satisfying the SAME average input budget. No feedback, shared
entanglement, product-state restriction, or energy cap after the channel. -/
def classicalPhotonRateAchievable {I J : Type} (weight : I → ℕ)
    (T : Matrix I I ℂ → Matrix J J ℂ) (N : ℝ) (R : ℝ≥0) : Prop :=
  ∀ epsilon delta : ℝ, 0 < epsilon → 0 < delta →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ c : PhotonConstrainedClassicalCode I J n,
        codeWithinBudget weight N c ∧ 1 - epsilon ≤ photonCodeSuccessProbability T c ∧
        (R : ℝ) - delta ≤ Real.log (c.messages : ℝ) / Real.log 2 / (n : ℝ)

/-- PDF p.1: operational classical capacity as an extended nonnegative
supremum. Empty rate sets give zero; unbounded sets give infinity. Neither g
nor a scalar capacity bound appears in this definition. -/
def classicalPhotonCapacityBits {I J : Type} (weight : I → ℕ)
    (T : Matrix I I ℂ → Matrix J J ℂ) (N : ℝ) : ℝ≥0∞ :=
  ⨆ R : {R : ℝ≥0 // classicalPhotonRateAchievable weight T N R},
    (R.val : ℝ≥0∞)

/-- PDF pp.1--2, Eq.(1) and Theorem 1: Holevo's coherent-signal rate in bits.
The accepted g uses natural logarithms and 0 log 0=0. -/
def coherentSignalRateBits (lam NE N : ℝ) : ℝ :=
  (g (lam * N + (1 - lam) * NE) - g ((1 - lam) * NE)) / Real.log 2

/-- PDF p.2, Eq.(3): finite numerical upper bound, not a capacity definition. -/
def thermalUpperBoundBits (lam NE N : ℝ) : ℝ :=
  g (lam * N / ((1 - lam) * NE + 1)) / Real.log 2

/-- PDF p.2, Lemma 1: the numerical upper-minus-lower gap in nats.
Source limit and strict derivative claims use Y>0, and X>0 where stated. -/
def thermalBoundGapNats (Y X : ℝ) : ℝ :=
  g (X / (Y + 1)) - g (X + Y) + g Y

/-! Sanity examples pin zero-energy/zero-noise boundaries and code domains.
Only definitions are checked here; no source theorem is proved. -/

example (lam NE : ℝ) : coherentSignalRateBits lam NE 0 = 0 := by
  simp [coherentSignalRateBits]

example (lam NE : ℝ) : thermalUpperBoundBits lam NE 0 = 0 := by
  simp [thermalUpperBoundBits, g]

example (Y : ℝ) : thermalBoundGapNats Y 0 = 0 := by
  simp [thermalBoundGapNats, g]

example (X : ℝ) : thermalBoundGapNats 0 X = 0 := by
  simp [thermalBoundGapNats, g]

example {I J : Type} {n : ℕ} (c : PhotonConstrainedClassicalCode I J n) :
    n ≠ 0 ∧ c.messages ≠ 0 := by
  exact ⟨Nat.ne_of_gt c.block_pos, Nat.ne_of_gt c.messages_pos⟩

example (I J : Type) : IsEmpty (PhotonConstrainedClassicalCode I J 0) :=
  ⟨fun c => (Nat.lt_irrefl 0) c.block_pos⟩

example {J : Type} (d : FiniteCollectivePOVM J 1) :
    d.effect 0 = ContinuousLinearMap.id ℂ (Hilbert J) := by
  simpa using d.total

example {I J : Type} (X : Matrix I I ℂ) :
    weightedPhotonExpectation (fun _ : I => 0) X = 0 := by
  simp [weightedPhotonExpectation]

end QAlgorithms.Papers.Independent.Bridge50.P28


