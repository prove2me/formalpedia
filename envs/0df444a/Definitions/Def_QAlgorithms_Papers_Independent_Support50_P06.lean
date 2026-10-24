-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06
-- name    : QAlgorithms_Papers_Independent_Support50_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T18:27:24.821169+00:00
-- url     : https://prove2.me/theorems/c13d3202-43c0-46c4-90d0-9cb9a8c9079a
-- title:
--   Definitions for Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality
-- statement:
--   The objects the formalized statements of *Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality* (arXiv:0801.0841) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `entropyParameter`: PDF p.4, (20). The real thermal parameter is used only for finite entropy and positive n. It is not the physical mean photon number.
--   - `entropyPhotonNumber`: PDF p.4, (20),(22). Infinite output entropy gives infinity before toReal. All theorems constructing finite comparison states require finite input entropy.
--   - `EpniAt`: PDF p.4, (22): the pointwise conjectured inequality, with independent ports implemented by mixedOutput. No energy condition is imposed.
--   - `EntropyPhotonNumberInequality`: PDF p.4, (22). This is a conjectural predicate, universally quantified on the finite-input-entropy domain used for the source's thermal comparisons.
--   - `CenteredPureInput`: PDF p.4, Conjecture 1: every annihilation expectation converges and is zero. The pure vector's normalization is separately required. This does not require finite photon energy or replace a divergent series by its tsum default.
--   - `MinimumOutputEntropyConjecture1`: PDF pp.4–5, Conjecture 1 and its attained value. The optimized a port is pure and centered; b is the identical thermal product. Arbitrary correlations within the pure n-mode input are allowed.
--   - `coherentMixture`: PDF p.4, (18). The accepted complexNormal N 0 has exactly the printed Lebesgue density when N>0 and is delta_0 when N=0.
--   - `totalEnergy`: PDF pp.2–3: total photon expectation across all n modes, including infinity. Uses the accepted actual diagonal photon expectation, with no cutoff.
--   - `BosonicPrivateCode`: PDF p.2, (4)–(5): uniform secret messages, arbitrary normalized mixed block states, a normalized decoder POVM, and independent private discrete randomness. A finite random alphabet embeds in this countable one with zero weights.
--   - `eveMessage`: PDF p.2, message secrecy: first average all private randomization at Eve.
--   - `eveAverage`: PDF p.2: Eve's unconditional state, averaging uniform messages.
--   - `messageLeakage`: PDF p.2, corrected (5): Holevo information of the MESSAGE, in nats. Finite code energy implies all of these message entropies are finite; the extended nonnegative subtraction does not turn an infinite entropy into zero.
--   - `randomizedPrivateCodePhotonBudget`: PDF pp.2–3: unconditional TOTAL input energy, averaged over uniform messages and private randomness. There is no separate constraint on any mode or codeword.
--   - `Decodes`: PDF p.2, (4): the source's strict success bound for every m,k, including unused random branches, rather than an average probability of error.
--   - `CoherentPrivateCode`: PDF p.3: single-use coherent signal states, tensorized over the block. The decoder can be collective and the amplitudes can vary across uses.
--   - `privateAchievable`: PDF pp.2–3: actual asymptotic private rate in nats per width-mode channel use. width=1 is the source channel. Grouping width parallel identical modes expresses additivity with the SAME total average budget. The definition contains no capacity formula or entropy conjecture. All choices precede m,k.
--   - `holevoMessagePrivacyCapacityNats`: PDF pp.2–3: operational private capacity, an extended nonnegative supremum. Empty feasible sets give zero and unbounded sets infinity, never a real default. The arbitrary-state capacity uses coherentOnly=false.
--   - `PrivateEnsemble`: PDF p.2, (6)–(7): finite auxiliary ensemble of arbitrary mixed n-mode inputs. Random preparation is absorbed into each conditional density. This retains arbitrary auxiliary weights, not just a uniform codebook.
--   - `finiteFockEnsembleBarycenter`: PDF p.2: average input density for the auxiliary ensemble.
--   - `ensembleEnergy`: PDF pp.2–3: the unconditional photon budget of a block ensemble.
--   - `ensemblePrivateInformation`: PDF p.2, (6): chi(T;B)-chi(T;E), including mixed conditional inputs. Finite average energy makes all positive-weight entropies finite; zero-weight terms contribute zero. The two receivers use the same vacuum dilation.
--   - `blockPrivateInformation`: PDF pp.2–3, (6)–(11): n-letter private-information supremum over all finite auxiliaries and arbitrary, possibly entangled, conditional input states. No absent numerical auxiliary-cardinality bound is invented. The supremum includes the finite-ensemble approximations used in the source's footnote 3.
--   - `vacuumLossCoherentInformationNats`: PDF p.3, (12): actual coherent information for the fixed vacuum dilation. The finite-energy optimization guarantees both output entropies finite; this finiteness is a theorem conclusion below, not an extra optimizing restriction.
--   - `coherentInformationMaximum`: PDF p.3, (12): unrestricted input optimization with the TOTAL photon budget. EReal retains empty/unbounded supremum semantics; Gaussianity is not assumed. The one-mode instance is Q^(1), not an operational quantum capacity.
--   - `gaussianPrivateInformation`: PDF p.3: difference of the two Holevo informations for the printed isotropic Gaussian coherent ensemble. Its average state is computed, not postulated. The theorem asserts zero individual output entropies, so the integrals exist.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, https://arxiv.org/abs/0801.0841v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11

/-!
Guha–Shapiro–Erkmen, arXiv:0801.0841v1. Full completed oscillator spaces,
natural logarithms, and extended nonnegative entropy. The imported paper modules
are pinned accepted libraries. No conjecture is asserted unconditionally.
The new private codes use message Holevo secrecy after private randomization;
this corrects the printed j=(m,k) in (5), as required by (6) and the capacity proof.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-!
Frozen-name repair audit (exact accepted source signatures checked):
* Eve uses imported `charlieMarginal (broadcast n eta X)` directly, preserving
  the common physical vacuum dilation. Gap48.P43.eveOutput instead requires a
  `PureDilation` unitary; no such extra witness is assumed here.
* `randomizedPrivateCodePhotonBudget` averages a countable private random seed
  with arbitrary weights. Next46.P32.codeEnergy takes a `BroadcastCode` and
  averages two finite uniform public message alphabets.
* `holevoMessagePrivacyCapacityNats` is energy constrained, full-Fock, Holevo
  message secrecy, with ENNReal extrema and strict branchwise decoding.
  Information100.P67.privateCapacity is finite-dimensional, unconstrained,
  fidelity based, in bits, with a real supremum. It cannot be substituted.
* `finiteFockEnsembleBarycenter` allows completed oscillator state spaces.
  Information100.P08.ensembleAverage requires a finite-dimensional state basis.
* `vacuumLossCoherentInformationNats` uses this fixed physical complement and
  extended spectral nats entropy on its finite-energy domain. Both frozen
  Information100 coherentInformation declarations require finite registers;
  P22 uses purification/bits and P39 also has a Renyi-order parameter.
The four distinct local bodies remain necessary; these are model distinctions,
not claims that same-named accepted definitions have been generalized by import.
-/

/-- PDF p.4, (20). The real thermal parameter is used only for finite entropy
and positive n. It is not the physical mean photon number. -/
def entropyParameter (n : ℕ) (S : ℝ≥0∞) : ℝ :=
  thermalEntropyInverse (S.toReal / (n : ℝ))

/-- PDF p.4, (20),(22). Infinite output entropy gives infinity before toReal.
All theorems constructing finite comparison states require finite input entropy. -/
def entropyPhotonNumber (n : ℕ) (S : ℝ≥0∞) : ℝ≥0∞ :=
  if S = ⊤ then ⊤ else ENNReal.ofReal (entropyParameter n S)

/-- PDF p.4, (22): the pointwise conjectured inequality, with independent
ports implemented by mixedOutput. No energy condition is imposed. -/
def EpniAt {n : ℕ} (eta : ℝ) (X Y : FockKernel n) : Prop :=
  ENNReal.ofReal eta * entropyPhotonNumber n (spectralEntropyNats X) +
      ENNReal.ofReal (1 - eta) * entropyPhotonNumber n (spectralEntropyNats Y) ≤
    entropyPhotonNumber n (spectralEntropyNats (mixedOutput n eta X Y))

/-- PDF p.4, (22). This is a conjectural predicate, universally quantified on
the finite-input-entropy domain used for the source's thermal comparisons. -/
def EntropyPhotonNumberInequality : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
    ∀ rhoA rhoB : State (NumberString n),
      spectralEntropyNats rhoA.coefficients ≠ ⊤ →
      spectralEntropyNats rhoB.coefficients ≠ ⊤ →
      EpniAt eta rhoA.coefficients rhoB.coefficients

/-- PDF p.4, Conjecture 1: every annihilation expectation converges and is
zero. The pure vector's normalization is separately required. This does not
require finite photon energy or replace a divergent series by its tsum default. -/
def CenteredPureInput {n : ℕ} (u : Hilbert (NumberString n)) : Prop :=
  ∀ i : Fin n, HasSum (fun a : NumberString n =>
    (Real.sqrt (a i + 1 : ℝ) : ℂ) * star (u a) *
      u (Function.update a i (a i + 1))) 0

/-- PDF pp.4–5, Conjecture 1 and its attained value. The optimized a port is
pure and centered; b is the identical thermal product. Arbitrary correlations
within the pure n-mode input are allowed. -/
def MinimumOutputEntropyConjecture1 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
    ∀ K : ℝ, 0 ≤ K →
      mixedOutput n eta (vacuum n) (identicalThermalKernel n K) =
        identicalThermalKernel n ((1 - eta) * K) ∧
      spectralEntropyNats (mixedOutput n eta (vacuum n) (identicalThermalKernel n K)) =
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ∧
      ∀ u : Hilbert (NumberString n), ‖u‖ = 1 → CenteredPureInput u →
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ≤
          spectralEntropyNats (mixedOutput n eta (rankOne u) (identicalThermalKernel n K))

/-- PDF p.4, (18). The accepted complexNormal N 0 has exactly the printed
Lebesgue density when N>0 and is delta_0 when N=0. -/
def coherentMixture (N : ℝ) : FockKernel 1 :=
  fun a b => ∫ alpha : ℂ, productCoherentKernel 1 (fun _ => alpha) a b
    ∂complexNormal N 0

/-- PDF pp.2–3: total photon expectation across all n modes, including infinity.
Uses the accepted actual diagonal photon expectation, with no cutoff. -/
def totalEnergy {n : ℕ} (X : FockKernel n) : ℝ≥0∞ :=
  ∑ i : Fin n, modeEnergy X i

/-- PDF p.2, (4)–(5): uniform secret messages, arbitrary normalized mixed block
states, a normalized decoder POVM, and independent private discrete randomness.
A finite random alphabet embeds in this countable one with zero weights. -/
structure BosonicPrivateCode (n M : ℕ) where
  block_positive : 0 < n
  messages_positive : 0 < M
  randomWeight : ℕ → ℝ
  random_nonnegative : ∀ k, 0 ≤ randomWeight k
  random_summable : Summable randomWeight
  random_total : (∑' k, randomWeight k) = 1
  encoder : Fin M → ℕ → State (NumberString n)
  decoder : FockPOVM (NumberString n) (Fin M)

/-- PDF p.2, message secrecy: first average all private randomization at Eve. -/
def eveMessage {n M : ℕ} (C : BosonicPrivateCode n M) (eta : ℝ)
    (m : Fin M) : FockKernel n :=
  fun a b => ∑' k : ℕ, (C.randomWeight k : ℂ) *
    (charlieMarginal (broadcast n eta (C.encoder m k).coefficients)) a b

/-- PDF p.2: Eve's unconditional state, averaging uniform messages. -/
def eveAverage {n M : ℕ} (C : BosonicPrivateCode n M) (eta : ℝ) : FockKernel n :=
  fun a b => (M : ℂ)⁻¹ * ∑ m : Fin M, eveMessage C eta m a b

/-- PDF p.2, corrected (5): Holevo information of the MESSAGE, in nats.
Finite code energy implies all of these message entropies are finite; the
extended nonnegative subtraction does not turn an infinite entropy into zero. -/
def messageLeakage {n M : ℕ} (C : BosonicPrivateCode n M) (eta : ℝ) : ℝ≥0∞ :=
  spectralEntropyNats (eveAverage C eta) -
    (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, spectralEntropyNats (eveMessage C eta m)

/-- PDF pp.2–3: unconditional TOTAL input energy, averaged over uniform messages
and private randomness. There is no separate constraint on any mode or codeword. -/
def randomizedPrivateCodePhotonBudget {n M : ℕ} (C : BosonicPrivateCode n M) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, ∑' k : ℕ,
    ENNReal.ofReal (C.randomWeight k) * totalEnergy (C.encoder m k).coefficients

/-- PDF p.2, (4): the source's strict success bound for every m,k, including
unused random branches, rather than an average probability of error. -/
def Decodes {n M : ℕ} (C : BosonicPrivateCode n M) (eta epsilon : ℝ) : Prop :=
  ∀ (m : Fin M) (k : ℕ), 1 - epsilon <
    realFockTracePair (pureLoss n eta (C.encoder m k).coefficients) (C.decoder.effect m)

/-- PDF p.3: single-use coherent signal states, tensorized over the block.
The decoder can be collective and the amplitudes can vary across uses. -/
def CoherentPrivateCode {n M : ℕ} (C : BosonicPrivateCode n M) : Prop :=
  ∃ alpha : Fin M → ℕ → Fin n → ℂ, ∀ m k,
    (C.encoder m k).coefficients = productCoherentKernel n (alpha m k)

/-- PDF pp.2–3: actual asymptotic private rate in nats per width-mode channel
use. width=1 is the source channel. Grouping width parallel identical modes
expresses additivity with the SAME total average budget. The definition contains
no capacity formula or entropy conjecture. All choices precede m,k. -/
def privateAchievable (width : ℕ) (eta Nbar : ℝ) (coherentOnly : Bool) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ M : ℕ, ∃ C : BosonicPrivateCode (n * width) M,
        randomizedPrivateCodePhotonBudget C ≤ ENNReal.ofReal (((n * width : ℕ) : ℝ) * Nbar) ∧
        Decodes C eta epsilon ∧ messageLeakage C eta ≤ ENNReal.ofReal epsilon ∧
        (coherentOnly = true → CoherentPrivateCode C) ∧
        R - delta ≤ Real.log (M : ℝ) / (n : ℝ)

/-- PDF pp.2–3: operational private capacity, an extended nonnegative supremum.
Empty feasible sets give zero and unbounded sets infinity, never a real default.
The arbitrary-state capacity uses coherentOnly=false. -/
def holevoMessagePrivacyCapacityNats (width : ℕ) (eta Nbar : ℝ) (coherentOnly : Bool := false) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ R : ℝ, privateAchievable width eta Nbar coherentOnly R ∧
    r = ENNReal.ofReal R}

/-- PDF p.2, (6)–(7): finite auxiliary ensemble of arbitrary mixed n-mode
inputs. Random preparation is absorbed into each conditional density. This
retains arbitrary auxiliary weights, not just a uniform codebook. -/
structure PrivateEnsemble (n L : ℕ) where
  alphabet_positive : 0 < L
  weight : Fin L → ℝ
  weight_nonnegative : ∀ j, 0 ≤ weight j
  weight_total : (∑ j, weight j) = 1
  input : Fin L → State (NumberString n)

/-- PDF p.2: average input density for the auxiliary ensemble. -/
def finiteFockEnsembleBarycenter {n L : ℕ} (A : PrivateEnsemble n L) : FockKernel n :=
  fun a b => ∑ j : Fin L, (A.weight j : ℂ) * (A.input j).coefficients a b

/-- PDF pp.2–3: the unconditional photon budget of a block ensemble. -/
def ensembleEnergy {n L : ℕ} (A : PrivateEnsemble n L) : ℝ≥0∞ :=
  ∑ j : Fin L, ENNReal.ofReal (A.weight j) * totalEnergy (A.input j).coefficients

/-- PDF p.2, (6): chi(T;B)-chi(T;E), including mixed conditional inputs.
Finite average energy makes all positive-weight entropies finite; zero-weight
terms contribute zero. The two receivers use the same vacuum dilation. -/
def ensemblePrivateInformation {n L : ℕ} (A : PrivateEnsemble n L) (eta : ℝ) : ℝ :=
  (spectralEntropyNats (pureLoss n eta (finiteFockEnsembleBarycenter A))).toReal -
    (spectralEntropyNats ((charlieMarginal (broadcast n eta (finiteFockEnsembleBarycenter A))))).toReal -
    ∑ j : Fin L, A.weight j *
      ((spectralEntropyNats (pureLoss n eta (A.input j).coefficients)).toReal -
        (spectralEntropyNats ((charlieMarginal (broadcast n eta (A.input j).coefficients)))).toReal)

/-- PDF pp.2–3, (6)–(11): n-letter private-information supremum over all
finite auxiliaries and arbitrary, possibly entangled, conditional input states.
No absent numerical auxiliary-cardinality bound is invented. The supremum
includes the finite-ensemble approximations used in the source's footnote 3. -/
def blockPrivateInformation (n : ℕ) (eta Nbar : ℝ) : EReal :=
  sSup {r : EReal | ∃ L : ℕ, ∃ A : PrivateEnsemble n L,
    ensembleEnergy A ≤ ENNReal.ofReal ((n : ℝ) * Nbar) ∧
    r = (ensemblePrivateInformation A eta : EReal)}

/-- PDF p.3, (12): actual coherent information for the fixed vacuum dilation.
The finite-energy optimization guarantees both output entropies finite; this
finiteness is a theorem conclusion below, not an extra optimizing restriction. -/
def vacuumLossCoherentInformationNats {n : ℕ} (eta : ℝ) (X : FockKernel n) : ℝ :=
  (spectralEntropyNats (pureLoss n eta X)).toReal -
    (spectralEntropyNats ((charlieMarginal (broadcast n eta X)))).toReal

/-- PDF p.3, (12): unrestricted input optimization with the TOTAL photon budget.
EReal retains empty/unbounded supremum semantics; Gaussianity is not assumed.
The one-mode instance is Q^(1), not an operational quantum capacity. -/
def coherentInformationMaximum (n : ℕ) (eta Nbar : ℝ) : EReal :=
  sSup {r : EReal | ∃ rho : State (NumberString n),
    totalEnergy rho.coefficients ≤ ENNReal.ofReal ((n : ℝ) * Nbar) ∧
    r = (vacuumLossCoherentInformationNats eta rho.coefficients : EReal)}

/-- PDF p.3: difference of the two Holevo informations for the printed isotropic
Gaussian coherent ensemble. Its average state is computed, not postulated.
The theorem asserts zero individual output entropies, so the integrals exist. -/
def gaussianPrivateInformation (eta Nbar : ℝ) : ℝ :=
  vacuumLossCoherentInformationNats eta (coherentMixture Nbar) -
    ∫ alpha : ℂ, vacuumLossCoherentInformationNats eta (productCoherentKernel 1 (fun _ => alpha))
      ∂complexNormal Nbar 0

example (n : ℕ) : entropyPhotonNumber n ⊤ = ⊤ := by
  simp [entropyPhotonNumber]

example (n : ℕ) : entropyPhotonNumber n 0 = 0 := by
  simp [entropyPhotonNumber, entropyParameter, thermalEntropyInverse]

example : g 0 = 0 := by simp [g]

example : complexNormal 0 (0 : ℂ) = Measure.dirac 0 := by simp [complexNormal]

example {n L : ℕ} (A : PrivateEnsemble n L) : (∑ j, A.weight j) = 1 :=
  A.weight_total

example {n M : ℕ} (C : BosonicPrivateCode n M) :
    (∑' k, C.randomWeight k) = 1 := C.random_total

example (X : FockKernel 0) : totalEnergy X = 0 := by
  simp [totalEnergy]

end QAlgorithms.Papers.Independent.Support50.P06


