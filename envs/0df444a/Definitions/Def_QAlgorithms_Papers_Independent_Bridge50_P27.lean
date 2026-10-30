-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P27
-- name    : QAlgorithms_Papers_Independent_Bridge50_P27
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:16:38.463493+00:00
-- url     : https://prove2.me/theorems/95aeae4d-1542-4fbf-9496-69fdba415aa5
-- title:
--   Definitions for Strong converse rates for classical communication over thermal and additive noise bosonic channels
-- statement:
--   The objects the formalized statements of *Strong converse rates for classical communication over thermal and additive noise bosonic channels* (arXiv:1312.3287) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `thermalBlock`: PDF pp.3–4, (1)–(3): n independent thermal uses on arbitrary n-mode inputs. The accepted splitter differs by a phase on the discarded environment only.
--   - `gaussianDisplacementWeight`: PDF p.5, (9): the density of n independent complex Gaussian displacements.
--   - `blockDisplacement`: PDF p.5, (9): tensor product of the actual Fock displacement matrices.
--   - `displacedKernel`: PDF p.5, (9): D(z) X D(z)^dagger on full Fock coefficients. The inner sum forms each row product before the outer operator product.
--   - `additiveBlock`: PDF p.5, (9): concrete memoryless additive channel; v=0 is the identity. For density inputs and v>0 the Gaussian-weighted scalar integrals are integrable: unitary conjugation has bounded matrix entries and the Gaussian has mass one.
--   - `ChannelSpec`: PDF pp.4–5: physical channel data; validity is imposed separately.
--   - `ValidChannel`: PDF pp.3–5: both endpoints and zero noise are included.
--   - `blockMap`: PDF pp.4–5: select the concrete physical block map, not arbitrary CPTP data.
--   - `noisePhotons`: PDF pp.4–5: output noise photons when the input is vacuum.
--   - `outputMean`: PDF pp.4–5: output mean per use at input mean NS.
--   - `coherentCodeRateBits`: PDF pp.4–5, (5),(11): coherent-state achievable rate, not a capacity definition.
--   - `giovannettiRateBound`: PDF pp.4–5, (7),(12): the scalar Giovannetti upper-bound expression.
--   - `lossBound`: PDF pp.5–6, (8),(13),(16): the scalar Koenig–Smith expression.
--   - `FockCommunicationCode`: PDF pp.7–10: equiprobable messages, arbitrary normalized block states, and one finite positive complete POVM on the full countable output space. M>0 is structural; n>0 is required by all operational uses of rate.
--   - `communicationRateBits`: PDF p.7: the actual message count fixes the rate in bits per physical use.
--   - `messageSuccess`: PDF pp.7–10: Born probability of correctly decoding one message.
--   - `decodingSuccessProbability`: PDF pp.7–10: success averaged uniformly over all messages.
--   - `totalPhotonCutoffMass`: PDF p.10, (29): the diagonal trace against the total-number projector Pi_L. On densities this is an absolutely summable subseries of a probability law.
--   - `codeShadow`: PDF pp.9–10, (30): average shadow, rather than a per-message restriction.
--   - `MeanConstraint`: PDF pp.8–9: a separate total-energy budget n*NS for EVERY codeword.
--   - `MaximumFamily`: PDF pp.9–10, (30): a family has vanishing average occupation deficit. The zero-length placeholder is unused; the constraint holds at every positive length.
--   - `StrongConverse`: PDF pp.10–18: all-code strong converse, with a fixed strict rate gap. Channel, NS and bound precede every family. Rate is eventually at least R.
--   - `MeanEnergyAchievable`: PDF pp.1,5,8: unassisted all-large-blocklength achievability with vanishing average error and per-codeword mean energy. Arbitrary entangled encodings allowed.
--   - `meanEnergyClassicalCapacity`: PDF pp.1,5, (13): operational classical capacity, as an extended supremum of achievable rates; no scalar capacity formula is built into the definition.
--   - `mixedWord`: PDF p.8, (26): dilute a coherent word by the physical n-mode vacuum.
--   - `flaggedAmplitude`: PDF p.9: the flag is the LAST of n+1 physical noisy uses, in orthogonal vacuum/one-photon states. Orthogonality normalizes the superposition even when its data coherent word overlaps the vacuum.
--   - `flaggedWord`: PDF p.9: the normalized flagged pure state, expressed by its full kernel.
--   - `discardFlagPOVM`: PDF p.9: the receiver ignores the last mode AFTER its noisy transmission.
--   - `PureEncoding`: PDF p.9: purity on the completed Hilbert space includes norm-one witnesses.
--   - `flagMixing`: PDF p.9: eventual choice solving (1-p)*nP+p=(n+1)*NS. Its denominator is positive only eventually; every use below supplies that guard.
--   - `ReliableCoherent`: PDF p.8, (24)–(25): actual reliable high-energy coherent codebooks and a vanishing pointwise error sequence. Existence of these data is a conclusion of each counterexample theorem, never an assumed success oracle.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, https://arxiv.org/abs/1312.3287v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

/-!
Bardhan and Wilde, arXiv:1312.3287v2. Completed countable Fock spaces,
normalized nuclear trace-class densities, arbitrary entangled block inputs,
and finite bounded POVMs. All rates here are in bits.
The independent-paper override permits imports from the pinned accepted library.
New definitions are local to this paper. Appendix A Lemma 2 is explicitly deferred.
Source corrections: PDF pp.12–15 require n*(mean+d5), not n*mean+d5;
PDF pp.15,17–18 require a minus sign before log2(n)/n in the final bracket.
Both corrections require independent moderation. Compilation is pending handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P27

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

-- Exact accepted definitions, checked against their complete source bodies.
open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)
open QAlgorithms.Papers.Independent.Renew46.P30 (photonTotal)
open QAlgorithms.Papers.Independent.Support50.P06 (totalEnergy)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace B
export QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel mixedOutput FockPOVM
   realFockTracePair productCoherentKernel vacuum)
end B

namespace S
export QAlgorithms.Papers.Independent.Dependency50.P33 (State rankOne)
end S

namespace D
export QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
end D

/-- PDF pp.3–4, (1)–(3): n independent thermal uses on arbitrary n-mode inputs.
The accepted splitter differs by a phase on the discarded environment only. -/
def thermalBlock (eta NB : ℝ) (n : ℕ) (X : B.FockKernel n) : B.FockKernel n :=
  B.mixedOutput n eta X (B.identicalThermalKernel n NB)

/-- PDF p.5, (9): the density of n independent complex Gaussian displacements. -/
def gaussianDisplacementWeight (v : ℝ) {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i, Real.exp (-Complex.normSq (z i) / v) / (Real.pi * v)

/-- PDF p.5, (9): tensor product of the actual Fock displacement matrices. -/
def blockDisplacement {n : ℕ} (z : Fin n → ℂ) (a b : B.NumberString n) : ℂ :=
  ∏ i, D.displacementMatrix (z i) (a i) (b i)

/-- PDF p.5, (9): D(z) X D(z)^dagger on full Fock coefficients.
The inner sum forms each row product before the outer operator product. -/
def displacedKernel {n : ℕ} (z : Fin n → ℂ) (X : B.FockKernel n) : B.FockKernel n :=
  fun a b => ∑' c, blockDisplacement z a c *
    (∑' d, X c d * star (blockDisplacement z b d))

/-- PDF p.5, (9): concrete memoryless additive channel; v=0 is the identity.
For density inputs and v>0 the Gaussian-weighted scalar integrals are integrable:
unitary conjugation has bounded matrix entries and the Gaussian has mass one. -/
def additiveBlock (v : ℝ) (n : ℕ) (X : B.FockKernel n) : B.FockKernel n :=
  if v = 0 then X else fun a b =>
    ∫ z : Fin n → ℂ, (gaussianDisplacementWeight v z : ℂ) * displacedKernel z X a b

/-- PDF pp.4–5: physical channel data; validity is imposed separately. -/
inductive ChannelSpec where
  | thermal (eta NB : ℝ)
  | additive (v : ℝ)

/-- PDF pp.3–5: both endpoints and zero noise are included. -/
def ValidChannel : ChannelSpec → Prop
  | .thermal eta NB => 0 ≤ eta ∧ eta ≤ 1 ∧ 0 ≤ NB
  | .additive v => 0 ≤ v

/-- PDF pp.4–5: select the concrete physical block map, not arbitrary CPTP data. -/
def blockMap : ChannelSpec → (n : ℕ) → B.FockKernel n → B.FockKernel n
  | .thermal eta NB => thermalBlock eta NB
  | .additive v => additiveBlock v

/-- PDF pp.4–5: output noise photons when the input is vacuum. -/
def noisePhotons : ChannelSpec → ℝ
  | .thermal eta NB => (1 - eta) * NB
  | .additive v => v

/-- PDF pp.4–5: output mean per use at input mean NS. -/
def outputMean (C : ChannelSpec) (NS : ℝ) : ℝ :=
  match C with
  | .thermal eta NB => eta * NS + (1 - eta) * NB
  | .additive v => NS + v

/-- PDF pp.4–5, (5),(11): coherent-state achievable rate, not a capacity definition. -/
def coherentCodeRateBits (C : ChannelSpec) (P : ℝ) : ℝ :=
  bosonicEntropy (outputMean C P) - bosonicEntropy (noisePhotons C)

/-- PDF pp.4–5, (7),(12): the scalar Giovannetti upper-bound expression. -/
def giovannettiRateBound (C : ChannelSpec) (NS : ℝ) : ℝ :=
  bosonicEntropy (outputMean C NS) - logBits (1 + 2 * noisePhotons C)

/-- PDF pp.5–6, (8),(13),(16): the scalar Koenig–Smith expression. -/
def lossBound (C : ChannelSpec) (NS : ℝ) : ℝ :=
  match C with
  | .thermal eta NB => bosonicEntropy (eta * NS / ((1 - eta) * NB + 1))
  | .additive v => bosonicEntropy (NS / (v + 1))

/-- PDF pp.7–10: equiprobable messages, arbitrary normalized block states,
and one finite positive complete POVM on the full countable output space.
M>0 is structural; n>0 is required by all operational uses of rate. -/
structure FockCommunicationCode (n M : ℕ) where
  messages_pos : 0 < M
  encoder : Fin M → S.State (B.NumberString n)
  decoder : B.FockPOVM (B.NumberString n) (Fin M)

/-- PDF p.7: the actual message count fixes the rate in bits per physical use. -/
def communicationRateBits (n M : ℕ) : ℝ := logBits (M : ℝ) / (n : ℝ)

/-- PDF pp.7–10: Born probability of correctly decoding one message. -/
def messageSuccess (C : ChannelSpec) {n M : ℕ} (K : FockCommunicationCode n M) (m : Fin M) : ℝ :=
  B.realFockTracePair (blockMap C n (K.encoder m).coefficients) (K.decoder.effect m)

/-- PDF pp.7–10: success averaged uniformly over all messages. -/
def decodingSuccessProbability (C : ChannelSpec) {n M : ℕ} (K : FockCommunicationCode n M) : ℝ :=
  (∑ m, messageSuccess C K m) / (M : ℝ)

/-- PDF p.10, (29): the diagonal trace against the total-number projector Pi_L.
On densities this is an absolutely summable subseries of a probability law. -/
def totalPhotonCutoffMass {n : ℕ} (L : ℕ) (X : B.FockKernel n) : ℝ :=
  ∑' a, if photonTotal a ≤ L then (X a a).re else 0

/-- PDF pp.9–10, (30): average shadow, rather than a per-message restriction. -/
def codeShadow {n M : ℕ} (K : FockCommunicationCode n M) (NS : ℝ) : ℝ :=
  (∑ m, totalPhotonCutoffMass (Nat.ceil ((n : ℝ) * NS)) (K.encoder m).coefficients) / (M : ℝ)

/-- PDF pp.8–9: a separate total-energy budget n*NS for EVERY codeword. -/
def MeanConstraint (NS : ℝ) {n M : ℕ} (K : FockCommunicationCode n M) : Prop :=
  ∀ m, totalEnergy (K.encoder m).coefficients ≤ ENNReal.ofReal ((n : ℝ) * NS)

/-- PDF pp.9–10, (30): a family has vanishing average occupation deficit.
The zero-length placeholder is unused; the constraint holds at every positive length. -/
def MaximumFamily (NS : ℝ) {M : ℕ → ℕ} (F : (n : ℕ) → FockCommunicationCode n (M n)) : Prop :=
  ∃ deficit : ℕ → ℝ, (∀ n, 0 ≤ deficit n ∧ deficit n ≤ 1) ∧
    Tendsto deficit atTop (𝓝 0) ∧
    ∀ n, 0 < n → 1 - deficit n ≤ codeShadow (F n) NS

/-- PDF pp.10–18: all-code strong converse, with a fixed strict rate gap.
Channel, NS and bound precede every family. Rate is eventually at least R. -/
def StrongConverse (C : ChannelSpec) (NS bound : ℝ) : Prop :=
  ∀ R : ℝ, bound < R → ∀ (M : ℕ → ℕ) (F : (n : ℕ) → FockCommunicationCode n (M n)),
    MaximumFamily NS F → (∀ᶠ n in atTop, R ≤ communicationRateBits n (M n)) →
    Tendsto (fun n => decodingSuccessProbability C (F n)) atTop (𝓝 0)

/-- PDF pp.1,5,8: unassisted all-large-blocklength achievability with vanishing
average error and per-codeword mean energy. Arbitrary entangled encodings allowed. -/
def MeanEnergyAchievable (C : ChannelSpec) (NS R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon : ℝ, 0 < epsilon → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ M : ℕ, ∃ K : FockCommunicationCode n M,
      MeanConstraint NS K ∧ R - slack ≤ communicationRateBits n M ∧ 1 - epsilon ≤ decodingSuccessProbability C K

/-- PDF pp.1,5, (13): operational classical capacity, as an extended supremum
of achievable rates; no scalar capacity formula is built into the definition. -/
def meanEnergyClassicalCapacity (C : ChannelSpec) (NS : ℝ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ R : NNReal, r = (R : ℝ≥0∞) ∧ MeanEnergyAchievable C NS (R : ℝ)}

/-- PDF p.8, (26): dilute a coherent word by the physical n-mode vacuum. -/
def mixedWord {n : ℕ} (alpha : Fin n → ℂ) (p : ℝ) : B.FockKernel n :=
  ((1 - p : ℝ) : ℂ) • B.productCoherentKernel n alpha + (p : ℂ) • B.vacuum n

/-- PDF p.9: the flag is the LAST of n+1 physical noisy uses, in orthogonal
vacuum/one-photon states. Orthogonality normalizes the superposition even when
its data coherent word overlaps the vacuum. -/
def flaggedAmplitude {n : ℕ} (alpha : Fin n → ℂ) (p : ℝ)
    (a : B.NumberString (n + 1)) : ℂ :=
  (Real.sqrt (1 - p) : ℂ) *
      (∏ i : Fin n, QAlgorithms.Papers.Independent.Dependency50.P39.coherentCoefficient
        (alpha i) (a (Fin.castSucc i))) * (if a (Fin.last n) = 0 then 1 else 0) +
    (Real.sqrt p : ℂ) *
      (if (∀ i : Fin n, a (Fin.castSucc i) = 0) ∧ a (Fin.last n) = 1 then 1 else 0)

/-- PDF p.9: the normalized flagged pure state, expressed by its full kernel. -/
def flaggedWord {n : ℕ} (alpha : Fin n → ℂ) (p : ℝ) : B.FockKernel (n + 1) :=
  fun a b => flaggedAmplitude alpha p a * star (flaggedAmplitude alpha p b)

/-- PDF p.9: the receiver ignores the last mode AFTER its noisy transmission. -/
def discardFlagPOVM {n M : ℕ} (E : B.FockPOVM (B.NumberString n) (Fin M))
    (m : Fin M) : B.FockKernel (n + 1) :=
  fun a b => E.effect m (fun i => a (Fin.castSucc i)) (fun i => b (Fin.castSucc i)) *
    (if a (Fin.last n) = b (Fin.last n) then 1 else 0)

/-- PDF p.9: purity on the completed Hilbert space includes norm-one witnesses. -/
def PureEncoding {n M : ℕ} (K : FockCommunicationCode n M) : Prop :=
  ∀ m, ∃ u : QAlgorithms.RealRegisters.Hilbert (B.NumberString n),
    ‖u‖ = 1 ∧ (K.encoder m).coefficients = S.rankOne u

/-- PDF p.9: eventual choice solving (1-p)*nP+p=(n+1)*NS.
Its denominator is positive only eventually; every use below supplies that guard. -/
def flagMixing (NS P : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * P - ((n + 1 : ℕ) : ℝ) * NS) / ((n : ℝ) * P - 1)

/-- PDF p.8, (24)–(25): actual reliable high-energy coherent codebooks and a
vanishing pointwise error sequence. Existence of these data is a conclusion
of each counterexample theorem, never an assumed success oracle. -/
def ReliableCoherent (C : ChannelSpec) (P : ℝ) {M : ℕ → ℕ}
    (F : (n : ℕ) → FockCommunicationCode n (M n))
    (alpha : (n : ℕ) → Fin (M n) → Fin n → ℂ) (epsilon : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ epsilon n ∧ epsilon n ≤ 1) ∧ Tendsto epsilon atTop (𝓝 0) ∧
    ∀ n, 0 < n → ∀ m,
      ((F n).encoder m).coefficients = B.productCoherentKernel n (alpha n m) ∧
      (∑ i, Complex.normSq (alpha n m i)) ≤ (n : ℝ) * P ∧
      1 - epsilon n ≤ messageSuccess C (F n) m

example : bosonicEntropy 0 = 0 := by simp [bosonicEntropy]

example (n : ℕ) (X : B.FockKernel n) : additiveBlock 0 n X = X := by
  simp [additiveBlock]

example : photonTotal (fun _ : Fin 0 => 0) = 0 := by simp [photonTotal]

example : photonTotal (fun _ : Fin 1 => 1) = 1 := by simp [photonTotal]

example : communicationRateBits 0 1 = 0 := by simp [communicationRateBits, logBits]

example (n : ℕ) (alpha : Fin n → ℂ) : mixedWord alpha 0 = B.productCoherentKernel n alpha := by
  simp [mixedWord]

example (NS P : ℝ) : flagMixing NS P 0 = NS := by simp [flagMixing]

end QAlgorithms.Papers.Independent.Bridge50.P27


