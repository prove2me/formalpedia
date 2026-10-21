-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
-- name    : QAlgorithms_Papers_Independent_Next46_P32
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T15:28:22.884+00:00
-- url     : https://prove2.me/theorems/00ac85ac-5b51-4d12-84a2-b7bd896804bc
-- title:
--   Definitions for Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture
-- statement:
--   The objects the formalized statements of *Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture* (arXiv:0706.3416) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NumberString`: Full n-mode number basis, PDF pp.3,7-8.
--   - `FockKernel`: Coefficients on the completed Fock space, not a finite matrix cutoff.
--   - `identicalThermalKernel`: PDF p.8: identical thermal modes of mean K, including K=0.
--   - `vacuum`: PDF pp.3,8: the fixed vacuum on every unused port.
--   - `productCoherentKernel`: PDF pp.4,12-13: full product coherent codeword, without truncation.
--   - `beamCoefficient`: PDF p.3, (14)-(15): Fock matrix of b=t a+r e, c=r a-t e. The finite sum stays within a conserved photon sector, never a global cutoff.
--   - `blockBeam`: Memoryless tensor product of the physical beam splitter, PDF p.3.
--   - `jointMix`: PDF pp.3,8: independent input ports, arbitrary correlations within each port. For each fixed output entry, photon conservation makes the input sums finite.
--   - `bobMarginal`: Partial trace over Charlie, PDF p.2. On the density domain this is summable.
--   - `charlieMarginal`: Partial trace over Bob, PDF p.2.
--   - `pureLoss`: Pure-loss intensity eta with fixed vacuum environment, PDF pp.3-4.
--   - `broadcast`: The two-receiver channel of (14)-(15), with independent vacuum environment.
--   - `lossyBroadcast`: PDF p.4: first discard intensity 1-etaB-etaC to vacuum, then split the remaining field. The physical theorem assumes 0<=etaC<etaB and etaB+etaC<1.
--   - `SpectralResolution`: Spectral resolution of a density on the completed number space. Zero weights may have zero vectors, permitting finite rank without fictitious states. Nonzero eigenvectors are orthonormal; all coefficients and total trace are fixed.
--   - `spectralEntropyNats`: PDF pp.3,7-8: spectral von Neumann entropy, including infinity. Every positive trace-class trace-one kernel has such a resolution, all with the same entropy. The infimum over an empty resolution type is infinity, never real zero.
--   - `husimi`: PDF p.8, (A1): Husimi density relative to ordinary complex Lebesgue measure.
--   - `wehrl`: PDF p.8, (A1): shifted Wehrl entropy. On a density pi^n Q<=1, so the integrand is nonnegative. The lintegral retains infinite entropy.
--   - `quadrature`: Real phase coordinates for the actual Husimi law.
--   - `Gaussian`: PDF pp.9-11: actual Gaussian densities, characterized equivalently by a Gaussian Husimi density. The state condition enforces quantum positivity; means are unrestricted, and intermode correlations are allowed.
--   - `mixedOutput`: Appendix A, PDF p.8: the first output of independent a,b ports.
--   - `StrongConjecture2`: Strong Conjecture 2, PDF p.8, globally quantified; it is only a predicate. The finite input entropy is an extended-real equality, and thermal attainment is included. No energy restriction or Gaussian restriction is imposed.
--   - `GaussianStrongConjecture1`: Gaussian Strong Conjecture 1, PDF pp.7,11. The noise consists of n IDENTICAL thermal states as explicitly used on p.11. Displacements of the optimized Gaussian a input are allowed. The value uses intensity 1-eta.
--   - `GaussianStrongConjecture2`: Gaussian Strong Conjecture 2, PDF pp.8-11: the optimized b input can have arbitrary intra-port Gaussian correlations and nonzero mean.
--   - `modeEnergy`: PDF p.5: unconditional expectation of photons in one mode, including infinity.
--   - `PositiveKernel`: Positive coefficient forms, used for finite-outcome POVMs on full Fock space.
--   - `FockPOVM`: PDF p.2, (10): separate finite-outcome POVMs. Positivity and finite sum identity imply each effect extends to a bounded operator between zero and I.
--   - `realFockTracePair`: Trace pairing of a trace-class kernel and a bounded effect.
--   - `BroadcastCode`: PDF pp.2-3: independent finite uniform messages. Bob's output type is explicit so that the source's stronger decoder and ordinary private decoding can share the physical encoder/POVM data without being identified.
--   - `codeEnergy`: PDF p.5: total block energy averaged uniformly over the whole codebook.
--   - `codeModeEnergy`: Per-use unconditional energy, the distinct supporting-objective constraint.
--   - `broadcastSuccessProbability`: Joint probability with separate POVMs, retaining physical BC correlations.
--   - `CoherentCode`: Product coherent encoding, PDF pp.4,12-13; the measurement may be collective within each receiver's n-mode block. This is not single-use decoding.
--   - `sourceAchievable`: Source achievability (PDF pp.2-3): Bob decodes (m,k), Charlie decodes k; error is bounded for EVERY pair. Rates come from actual message cardinalities. Positive thresholds exclude n=0. Setting coherentOnly restricts the encoder.
--   - `sourceRegion`: PDF p.3: convex hull of the closure of achievable rate pairs.
--   - `privateAchievablePerUse`: Supporting objective only: ordinary private messages, average joint error, full-Fock encoders, separate POVMs, and unconditional energy <=Nbar in EACH use. No equivalence to sourceAchievable is asserted. No external rate bound is assumed.
--   - `privateRegionPerUse`: Ordinary private-message region of the supporting objective.
--   - `thermalRegion`: PDF p.4, (16)-(17), with independent receiver intensity fractions.
--   - `complexNormal`: PDF p.4, (18)-(19): isotropic complex normal law, total complex variance V. The zero-variance case is the Dirac mass, not a singular density formula.
--   - `conditionalCoherentMixture`: PDF p.4: conditional coherent ensemble at the receiver of intensity eta.
--   - `averageCoherent`: PDF p.4: unconditional coherent ensemble at that receiver.
--   - `conditionalEntropyAverage`: Real, finite conditional entropy average for the Gaussian ensembles of p.4. The theorem below also asserts finiteness pointwise and scalar integrability.
--   - `homodyneLaw`: PDF pp.5-6: fixed real-quadrature homodyne observations with noise variance 1/4 independently in every use. Complex modulation is permitted; its imaginary part consumes energy but does not affect this observation.
--   - `heterodyneLaw`: PDF p.6: heterodyne noise has variance 1/2 in EACH real quadrature, so total complex variance one. The density is exp(-|z-mu|^2)/pi.
--   - `OpticalDetectionCode`: Section V uses the classical private-message convention from Section II: product coherent modulation and separate fixed single-use optical detection, followed by arbitrary measurable classical block decoders.
--   - `detectionEnergy`: The coherent alphabet's unconditional block photon energy.
--   - `detectionSuccess`: Conditional receiver noises are independent, so conditional joint success is the product of their two classical decoder success probabilities.
--   - `detectionAchievable`: Section II, PDF p.2 and Section V, PDF pp.5-6: ordinary private-message achievability under the specified fixed optical measurement. Finite messages are independent uniform; the overall error is averaged over their pairs.
--   - `detectionRegion`: Receiver-restricted classical capacity: closure of achievable pairs, p.2.
--   - `homodyneRateRegion`: PDF p.6, (36)-(37), in nats per use.
--   - `heterodyneRateRegion`: PDF p.6, (38)-(39), total complex noise variance one.
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, https://arxiv.org/abs/0706.3416v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

/-!
Guha, Shapiro and Erkmen, arXiv:0706.3416v1. All rates and entropies are in
nats. Basis labels are arbitrary photon-number strings; there is no cutoff.
The accepted nuclear trace-class state interface is reused. The exact thermal
entropy and coherent coefficients are imported from the pinned accepted library.
New channel, measurement, coding and entropy interfaces are local to this paper.
The nonduality comparison is deferred in HARD.md. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-!
Reuse audit: `g` is exactly Claimed50.P39.g (nats), and
`coherentCoefficient` is exactly Dependency50.P39.coherentCoefficient.
Distinct interfaces retain complete local bodies under descriptive names.
FockKernel is a countable complex operator array, not Dependency50.P32.Kernel
(a finite real conditional law); identicalThermalKernel is a state, not
Claimed50.P39.thermal (a channel); productCoherentKernel is a projector, not
Information100.P59.coherent (a Hamiltonian superoperator). spectralEntropyNats
is extended n-mode entropy, unlike the frozen finite-matrix/relative entropies.
FockPOVM has a countable input basis; realFockTracePair pairs coefficient arrays
and takes the real part; broadcastSuccessProbability uses two receiver POVMs.
conditionalCoherentMixture is a density ensemble, unlike the frozen conditional
coherent information. OpticalDetectionCode uses complex amplitudes and the
source block-average energy convention, unlike the frozen amplifier detection
code with measured-quadrature inputs and per-use energy. ASSESSMENT.json gives
individual decisions and exact checked library locators.
-/

/-- Full n-mode number basis, PDF pp.3,7-8. -/
abbrev NumberString (n : ℕ) := Fin n → ℕ

/-- Coefficients on the completed Fock space, not a finite matrix cutoff. -/
abbrev FockKernel (n : ℕ) := Matrix (NumberString n) (NumberString n) ℂ

/-- PDF p.8: identical thermal modes of mean K, including K=0. -/
def identicalThermalKernel (n : ℕ) (K : ℝ) : FockKernel n :=
  fun a b => if a = b then
    ((∏ i : Fin n, (K / (K + 1)) ^ (a i) / (K + 1) : ℝ) : ℂ) else 0

/-- PDF pp.3,8: the fixed vacuum on every unused port. -/
def vacuum (n : ℕ) : FockKernel n :=
  fun a b => if a = 0 ∧ b = 0 then 1 else 0

/-- PDF pp.4,12-13: full product coherent codeword, without truncation. -/
def productCoherentKernel (n : ℕ) (alpha : Fin n → ℂ) : FockKernel n :=
  fun a b => (∏ i, coherentCoefficient (alpha i) (a i)) *
    star (∏ i, coherentCoefficient (alpha i) (b i))

/-- PDF p.3, (14)-(15): Fock matrix of b=t a+r e, c=r a-t e.
The finite sum stays within a conserved photon sector, never a global cutoff. -/
def beamCoefficient (eta : ℝ) (m l p q : ℕ) : ℝ :=
  if m + l = p + q then
    Real.sqrt (((Nat.factorial m : ℝ) * (Nat.factorial l : ℝ)) /
      ((Nat.factorial p : ℝ) * (Nat.factorial q : ℝ))) *
    ∑ u ∈ Finset.range (p + 1),
      if u ≤ m ∧ m - u ≤ q then
        (Nat.choose p u : ℝ) * (Nat.choose q (m - u) : ℝ) *
        Real.sqrt eta ^ u * Real.sqrt (1 - eta) ^ (p - u + (m - u)) *
        (-Real.sqrt eta) ^ (q - (m - u))
      else 0
  else 0

/-- Memoryless tensor product of the physical beam splitter, PDF p.3. -/
def blockBeam (n : ℕ) (eta : ℝ)
    (out inp : NumberString n × NumberString n) : ℂ :=
  ((∏ i, beamCoefficient eta (out.1 i) (out.2 i) (inp.1 i) (inp.2 i) : ℝ) : ℂ)

/-- PDF pp.3,8: independent input ports, arbitrary correlations within each port.
For each fixed output entry, photon conservation makes the input sums finite. -/
def jointMix (n : ℕ) (eta : ℝ) (X Y : FockKernel n) :
    Matrix (NumberString n × NumberString n) (NumberString n × NumberString n) ℂ :=
  fun u v => ∑' a : NumberString n × NumberString n,
    ∑' b : NumberString n × NumberString n,
      blockBeam n eta u a * productCoeff X Y a b * star (blockBeam n eta v b)

/-- Partial trace over Charlie, PDF p.2. On the density domain this is summable. -/
def bobMarginal {n : ℕ}
    (X : Matrix (NumberString n × NumberString n) (NumberString n × NumberString n) ℂ) :
    FockKernel n := fun a b => ∑' e, X (a, e) (b, e)

/-- Partial trace over Bob, PDF p.2. -/
def charlieMarginal {n : ℕ}
    (X : Matrix (NumberString n × NumberString n) (NumberString n × NumberString n) ℂ) :
    FockKernel n := fun a b => ∑' e, X (e, a) (e, b)

/-- Pure-loss intensity eta with fixed vacuum environment, PDF pp.3-4. -/
def pureLoss (n : ℕ) (eta : ℝ) (X : FockKernel n) : FockKernel n :=
  bobMarginal (jointMix n eta X (vacuum n))

/-- The two-receiver channel of (14)-(15), with independent vacuum environment. -/
def broadcast (n : ℕ) (eta : ℝ) (X : FockKernel n) :=
  jointMix n eta X (vacuum n)

/-- PDF p.4: first discard intensity 1-etaB-etaC to vacuum, then split the
remaining field. The physical theorem assumes 0<=etaC<etaB and etaB+etaC<1. -/
def lossyBroadcast (n : ℕ) (etaB etaC : ℝ) (X : FockKernel n) :=
  broadcast n (etaB / (etaB + etaC)) (pureLoss n (etaB + etaC) X)

/-- Spectral resolution of a density on the completed number space. Zero
weights may have zero vectors, permitting finite rank without fictitious states.
Nonzero eigenvectors are orthonormal; all coefficients and total trace are fixed. -/
structure SpectralResolution {n : ℕ} (X : FockKernel n) where
  weight : ℕ → NNReal
  vector : ℕ → Hilbert (NumberString n)
  summable : Summable (fun j => (weight j : ℝ))
  total : (∑' j, (weight j : ℝ)) = 1
  norm_one : ∀ j, 0 < weight j → ‖vector j‖ = 1
  orthogonal : ∀ i j, i ≠ j → 0 < weight i → 0 < weight j →
    inner (𝕜 := ℂ) (vector i) (vector j) = 0
  coefficients : ∀ a b, X a b = ∑' j,
    ((weight j : ℝ) : ℂ) * vector j a * star (vector j b)

/-- PDF pp.3,7-8: spectral von Neumann entropy, including infinity. Every
positive trace-class trace-one kernel has such a resolution, all with the same
entropy. The infimum over an empty resolution type is infinity, never real zero. -/
def spectralEntropyNats {n : ℕ} (X : FockKernel n) : ℝ≥0∞ :=
  ⨅ d : SpectralResolution X,
    ∑' j, ENNReal.ofReal (-(d.weight j : ℝ) * Real.log (d.weight j : ℝ))

/-- PDF p.8, (A1): Husimi density relative to ordinary complex Lebesgue measure. -/
def husimi {n : ℕ} (X : FockKernel n) (alpha : Fin n → ℂ) : ℝ :=
  (∑' a : NumberString n, ∑' b : NumberString n,
    star (∏ i, coherentCoefficient (alpha i) (a i)) * X a b *
      (∏ i, coherentCoefficient (alpha i) (b i))).re / Real.pi ^ n

/-- PDF p.8, (A1): shifted Wehrl entropy. On a density pi^n Q<=1, so the
integrand is nonnegative. The lintegral retains infinite entropy. -/
def wehrl {n : ℕ} (X : FockKernel n) : ℝ≥0∞ :=
  ∫⁻ alpha : Fin n → ℂ,
    ENNReal.ofReal (-husimi X alpha * Real.log (Real.pi ^ n * husimi X alpha))

/-- Real phase coordinates for the actual Husimi law. -/
def quadrature {n : ℕ} (alpha : Fin n → ℂ) (i : Fin n × Fin 2) : ℝ :=
  if i.2 = 0 then (alpha i.1).re else (alpha i.1).im

/-- PDF pp.9-11: actual Gaussian densities, characterized equivalently by a
Gaussian Husimi density. The state condition enforces quantum positivity;
means are unrestricted, and intermode correlations are allowed. -/
def Gaussian {n : ℕ} (X : FockKernel n) : Prop :=
  IsDensity X ∧ ∃ (mu : Fin n → ℂ) (A : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (c : ℝ), A.IsSymm ∧ A.PosDef ∧ 0 < c ∧ ∀ alpha,
    husimi X alpha = c * Real.exp
      (-(∑ i, ∑ j, quadrature (alpha - mu) i * A i j * quadrature (alpha - mu) j))

/-- Appendix A, PDF p.8: the first output of independent a,b ports. -/
def mixedOutput (n : ℕ) (eta : ℝ) (X Y : FockKernel n) : FockKernel n :=
  bobMarginal (jointMix n eta X Y)

/-- Strong Conjecture 2, PDF p.8, globally quantified; it is only a predicate.
The finite input entropy is an extended-real equality, and thermal attainment
is included. No energy restriction or Gaussian restriction is imposed. -/
def StrongConjecture2 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
    ∀ K : ℝ, 0 ≤ K →
      spectralEntropyNats (identicalThermalKernel n K) = ENNReal.ofReal ((n : ℝ) * g K) ∧
      spectralEntropyNats (mixedOutput n eta (vacuum n) (identicalThermalKernel n K)) =
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ∧
      ∀ rho : State (NumberString n),
        spectralEntropyNats rho.coefficients = ENNReal.ofReal ((n : ℝ) * g K) →
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ≤
          spectralEntropyNats (mixedOutput n eta (vacuum n) rho.coefficients)

/-- Gaussian Strong Conjecture 1, PDF pp.7,11. The noise consists of n
IDENTICAL thermal states as explicitly used on p.11. Displacements of the
optimized Gaussian a input are allowed. The value uses intensity 1-eta. -/
def GaussianStrongConjecture1 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
    ∀ K : ℝ, 0 ≤ K →
      spectralEntropyNats (mixedOutput n eta (vacuum n) (identicalThermalKernel n K)) =
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ∧
      ∀ rho : State (NumberString n), Gaussian rho.coefficients →
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ≤
          spectralEntropyNats (mixedOutput n eta rho.coefficients (identicalThermalKernel n K))

/-- Gaussian Strong Conjecture 2, PDF pp.8-11: the optimized b input can have
arbitrary intra-port Gaussian correlations and nonzero mean. -/
def GaussianStrongConjecture2 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 →
    ∀ K : ℝ, 0 ≤ K →
      spectralEntropyNats (identicalThermalKernel n K) = ENNReal.ofReal ((n : ℝ) * g K) ∧
      spectralEntropyNats (mixedOutput n eta (vacuum n) (identicalThermalKernel n K)) =
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ∧
      ∀ rho : State (NumberString n), Gaussian rho.coefficients →
        spectralEntropyNats rho.coefficients = ENNReal.ofReal ((n : ℝ) * g K) →
        ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * K)) ≤
          spectralEntropyNats (mixedOutput n eta (vacuum n) rho.coefficients)

/-- PDF p.5: unconditional expectation of photons in one mode, including infinity. -/
def modeEnergy {n : ℕ} (X : FockKernel n) (i : Fin n) : ℝ≥0∞ :=
  ∑' a : NumberString n, ENNReal.ofReal ((a i : ℝ) * (X a a).re)

/-- Positive coefficient forms, used for finite-outcome POVMs on full Fock space. -/
def PositiveKernel {I : Type} (E : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re

/-- PDF p.2, (10): separate finite-outcome POVMs. Positivity and finite sum
identity imply each effect extends to a bounded operator between zero and I. -/
structure FockPOVM (I O : Type) [Fintype O] where
  effect : O → Matrix I I ℂ
  positive : ∀ o, PositiveKernel (effect o)
  complete : ∀ a b, (∑ o, effect o a b) = if a = b then 1 else 0

/-- Trace pairing of a trace-class kernel and a bounded effect. -/
def realFockTracePair {I : Type} (X E : Matrix I I ℂ) : ℝ :=
  (∑' a, ∑' b, X a b * E b a).re

/-- PDF pp.2-3: independent finite uniform messages. Bob's output type is
explicit so that the source's stronger decoder and ordinary private decoding
can share the physical encoder/POVM data without being identified. -/
structure BroadcastCode (n MB MC : ℕ) (O : Type) [Fintype O] where
  bob_nonempty : 0 < MB
  charlie_nonempty : 0 < MC
  encoder : Fin MB → Fin MC → State (NumberString n)
  bob : FockPOVM (NumberString n) O
  charlie : FockPOVM (NumberString n) (Fin MC)

/-- PDF p.5: total block energy averaged uniformly over the whole codebook. -/
def codeEnergy {n MB MC : ℕ} {O : Type} [Fintype O]
    (C : BroadcastCode n MB MC O) : ℝ≥0∞ :=
  (∑ m, ∑ k, ∑ i, modeEnergy (C.encoder m k).coefficients i) /
    ((MB * MC : ℕ) : ℝ≥0∞)

/-- Per-use unconditional energy, the distinct supporting-objective constraint. -/
def codeModeEnergy {n MB MC : ℕ} {O : Type} [Fintype O]
    (C : BroadcastCode n MB MC O) (i : Fin n) : ℝ≥0∞ :=
  (∑ m, ∑ k, modeEnergy (C.encoder m k).coefficients i) /
    ((MB * MC : ℕ) : ℝ≥0∞)

/-- Joint probability with separate POVMs, retaining physical BC correlations. -/
def broadcastSuccessProbability {n MB MC : ℕ} {O : Type} [Fintype O]
    (C : BroadcastCode n MB MC O)
    (channel : FockKernel n → Matrix (NumberString n × NumberString n)
      (NumberString n × NumberString n) ℂ) (m : Fin MB) (k : Fin MC) (o : O) : ℝ :=
  realFockTracePair (channel (C.encoder m k).coefficients)
    (productCoeff (C.bob.effect o) (C.charlie.effect k))

/-- Product coherent encoding, PDF pp.4,12-13; the measurement may be collective
within each receiver's n-mode block. This is not single-use decoding. -/
def CoherentCode {n MB MC : ℕ} {O : Type} [Fintype O]
    (C : BroadcastCode n MB MC O) : Prop :=
  ∃ alpha : Fin MB → Fin MC → Fin n → ℂ, ∀ m k,
    (C.encoder m k).coefficients = productCoherentKernel n (alpha m k)

/-- Source achievability (PDF pp.2-3): Bob decodes (m,k), Charlie decodes k;
error is bounded for EVERY pair. Rates come from actual message cardinalities.
Positive thresholds exclude n=0. Setting coherentOnly restricts the encoder. -/
def sourceAchievable
    (channel : (n : ℕ) → FockKernel n → Matrix (NumberString n × NumberString n)
      (NumberString n × NumberString n) ℂ)
    (Nbar : ℝ) (coherentOnly : Bool) (R : ℝ × ℝ) : Prop :=
  0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∀ epsilon : ℝ, 0 < epsilon →
    ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ MB MC : ℕ, ∃ C : BroadcastCode n MB MC (Fin MB × Fin MC),
        codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar) ∧
        (coherentOnly = true → CoherentCode C) ∧
        R.1 - delta ≤ Real.log (MB : ℝ) / (n : ℝ) ∧
        R.2 - delta ≤ Real.log (MC : ℝ) / (n : ℝ) ∧
        ∀ m k, 1 - epsilon ≤ broadcastSuccessProbability C (channel n) m k (m, k)

/-- PDF p.3: convex hull of the closure of achievable rate pairs. -/
def sourceRegion
    (channel : (n : ℕ) → FockKernel n → Matrix (NumberString n × NumberString n)
      (NumberString n × NumberString n) ℂ)
    (Nbar : ℝ) (coherentOnly : Bool := false) : Set (ℝ × ℝ) :=
  convexHull ℝ (closure {R | sourceAchievable channel Nbar coherentOnly R})

/-- Supporting objective only: ordinary private messages, average joint error,
full-Fock encoders, separate POVMs, and unconditional energy <=Nbar in EACH use.
No equivalence to sourceAchievable is asserted. No external rate bound is assumed. -/
def privateAchievablePerUse (eta Nbar : ℝ) (R : ℝ × ℝ) : Prop :=
  0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∀ epsilon : ℝ, 0 < epsilon →
    ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ MB MC : ℕ, ∃ C : BroadcastCode n MB MC (Fin MB),
        (∀ i, codeModeEnergy C i ≤ ENNReal.ofReal Nbar) ∧
        R.1 - delta ≤ Real.log (MB : ℝ) / (n : ℝ) ∧
        R.2 - delta ≤ Real.log (MC : ℝ) / (n : ℝ) ∧
        1 - epsilon ≤ (∑ m, ∑ k,
          broadcastSuccessProbability C (broadcast n eta) m k m) / ((MB * MC : ℕ) : ℝ)

/-- Ordinary private-message region of the supporting objective. -/
def privateRegionPerUse (eta Nbar : ℝ) : Set (ℝ × ℝ) :=
  closure {R | privateAchievablePerUse eta Nbar R}

/-- PDF p.4, (16)-(17), with independent receiver intensity fractions. -/
def thermalRegion (etaB etaC Nbar : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ beta : ℝ, 0 ≤ beta ∧ beta ≤ 1 ∧
    R.1 ≤ g (etaB * beta * Nbar) ∧
    R.2 ≤ g (etaC * Nbar) - g (etaC * beta * Nbar)}

/-- PDF p.4, (18)-(19): isotropic complex normal law, total complex variance V.
The zero-variance case is the Dirac mass, not a singular density formula. -/
def complexNormal (V : ℝ) (mu : ℂ) : Measure ℂ :=
  if V = 0 then Measure.dirac mu else
    volume.withDensity (fun z =>
      ENNReal.ofReal (Real.exp (-Complex.normSq (z - mu) / V) / (Real.pi * V)))

/-- PDF p.4: conditional coherent ensemble at the receiver of intensity eta. -/
def conditionalCoherentMixture (eta beta Nbar : ℝ) (t : ℂ) : FockKernel 1 :=
  fun a b => ∫ alpha : ℂ,
    productCoherentKernel 1 (fun _ => (Real.sqrt eta : ℂ) * alpha) a b
      ∂complexNormal (Nbar * beta) ((Real.sqrt (1 - beta) : ℂ) * t)

/-- PDF p.4: unconditional coherent ensemble at that receiver. -/
def averageCoherent (eta beta Nbar : ℝ) : FockKernel 1 :=
  fun a b => ∫ t : ℂ, conditionalCoherentMixture eta beta Nbar t a b
    ∂complexNormal Nbar 0

/-- Real, finite conditional entropy average for the Gaussian ensembles of p.4.
The theorem below also asserts finiteness pointwise and scalar integrability. -/
def conditionalEntropyAverage (eta beta Nbar : ℝ) : ℝ :=
  ∫ t : ℂ, (spectralEntropyNats (conditionalCoherentMixture eta beta Nbar t)).toReal
    ∂complexNormal Nbar 0

/-- PDF pp.5-6: fixed real-quadrature homodyne observations with noise
variance 1/4 independently in every use. Complex modulation is permitted;
its imaginary part consumes energy but does not affect this observation. -/
def homodyneLaw (n : ℕ) (eta : ℝ) (alpha : Fin n → ℂ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun y => ENNReal.ofReal (∏ i,
    Real.sqrt (2 / Real.pi) *
      Real.exp (-2 * (y i - Real.sqrt eta * (alpha i).re) ^ 2)))

/-- PDF p.6: heterodyne noise has variance 1/2 in EACH real quadrature,
so total complex variance one. The density is exp(-|z-mu|^2)/pi. -/
def heterodyneLaw (n : ℕ) (eta : ℝ) (alpha : Fin n → ℂ) : Measure (Fin n → ℂ) :=
  volume.withDensity (fun y => ENNReal.ofReal (∏ i,
    Real.exp (-Complex.normSq (y i - (Real.sqrt eta : ℂ) * alpha i)) / Real.pi))

/-- Section V uses the classical private-message convention from Section II:
product coherent modulation and separate fixed single-use optical detection,
followed by arbitrary measurable classical block decoders. -/
structure OpticalDetectionCode (X : Type) [MeasurableSpace X] (n MB MC : ℕ) where
  bob_nonempty : 0 < MB
  charlie_nonempty : 0 < MC
  amplitude : Fin MB → Fin MC → Fin n → ℂ
  bob : (Fin n → X) → Fin MB
  charlie : (Fin n → X) → Fin MC
  bob_measurable : ∀ m, MeasurableSet {y | bob y = m}
  charlie_measurable : ∀ k, MeasurableSet {y | charlie y = k}

/-- The coherent alphabet's unconditional block photon energy. -/
def detectionEnergy {X : Type} [MeasurableSpace X] {n MB MC : ℕ}
    (C : OpticalDetectionCode X n MB MC) : ℝ :=
  (∑ m, ∑ k, ∑ i, Complex.normSq (C.amplitude m k i)) / ((MB * MC : ℕ) : ℝ)

/-- Conditional receiver noises are independent, so conditional joint success
is the product of their two classical decoder success probabilities. -/
def detectionSuccess {X : Type} [MeasurableSpace X] {n MB MC : ℕ}
    (law : (n : ℕ) → ℝ → (Fin n → ℂ) → Measure (Fin n → X))
    (eta : ℝ) (C : OpticalDetectionCode X n MB MC) (m : Fin MB) (k : Fin MC) : ℝ≥0∞ :=
  law n eta (C.amplitude m k) {y | C.bob y = m} *
    law n (1 - eta) (C.amplitude m k) {y | C.charlie y = k}

/-- Section II, PDF p.2 and Section V, PDF pp.5-6: ordinary private-message
achievability under the specified fixed optical measurement. Finite messages
are independent uniform; the overall error is averaged over their pairs. -/
def detectionAchievable {X : Type} [MeasurableSpace X]
    (law : (n : ℕ) → ℝ → (Fin n → ℂ) → Measure (Fin n → X))
    (eta Nbar : ℝ) (R : ℝ × ℝ) : Prop :=
  0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∀ epsilon : ℝ, 0 < epsilon →
    ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ MB MC : ℕ, ∃ C : OpticalDetectionCode X n MB MC,
        detectionEnergy C ≤ (n : ℝ) * Nbar ∧
        R.1 - delta ≤ Real.log (MB : ℝ) / (n : ℝ) ∧
        R.2 - delta ≤ Real.log (MC : ℝ) / (n : ℝ) ∧
        ENNReal.ofReal (1 - epsilon) ≤
          (∑ m, ∑ k, detectionSuccess law eta C m k) / ((MB * MC : ℕ) : ℝ≥0∞)

/-- Receiver-restricted classical capacity: closure of achievable pairs, p.2. -/
def detectionRegion {X : Type} [MeasurableSpace X]
    (law : (n : ℕ) → ℝ → (Fin n → ℂ) → Measure (Fin n → X))
    (eta Nbar : ℝ) : Set (ℝ × ℝ) :=
  closure {R | detectionAchievable law eta Nbar R}

/-- PDF p.6, (36)-(37), in nats per use. -/
def homodyneRateRegion (eta Nbar : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ beta : ℝ, 0 ≤ beta ∧ beta ≤ 1 ∧
    R.1 ≤ Real.log (1 + 4 * eta * beta * Nbar) / 2 ∧
    R.2 ≤ Real.log (1 + 4 * (1 - eta) * (1 - beta) * Nbar /
      (1 + 4 * (1 - eta) * beta * Nbar)) / 2}

/-- PDF p.6, (38)-(39), total complex noise variance one. -/
def heterodyneRateRegion (eta Nbar : ℝ) : Set (ℝ × ℝ) :=
  {R | 0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∃ beta : ℝ, 0 ≤ beta ∧ beta ≤ 1 ∧
    R.1 ≤ Real.log (1 + eta * beta * Nbar) ∧
    R.2 ≤ Real.log (1 + (1 - eta) * (1 - beta) * Nbar /
      (1 + (1 - eta) * beta * Nbar))}

/-! Sanity examples concern definitions only, never the source results. -/

example : g 0 = 0 := by simp [g]

example (mu : ℂ) : complexNormal 0 mu = Measure.dirac mu := by
  simp [complexNormal]

example (n : ℕ) : vacuum n (0 : NumberString n) 0 = 1 := by
  simp [vacuum]

example (eta : ℝ) : beamCoefficient eta 0 0 0 0 = 1 := by
  simp [beamCoefficient]

example (etaB etaC : ℝ) : (0, 0) ∈ thermalRegion etaB etaC 0 := by
  refine ⟨le_rfl, le_rfl, 0, le_rfl, zero_le_one, ?_, ?_⟩ <;>
    simp [g]

example (n : ℕ) (a b : NumberString n) :
    productCoherentKernel n (fun _ => 0) a b =
      (∏ i, coherentCoefficient 0 (a i)) * star (∏ i, coherentCoefficient 0 (b i)) := rfl

/-- The physical reflection sign in (15) on the environmental one-photon ket. -/
example : beamCoefficient 1 0 1 0 1 = -1 := by
  norm_num [beamCoefficient, Finset.sum_range_succ]

/-- At intensity zero the signal photon goes to Charlie with positive phase. -/
example : beamCoefficient 0 0 1 1 0 = 1 := by
  norm_num [beamCoefficient, Finset.sum_range_succ]

example (eta : ℝ) : blockBeam 0 eta (0, 0) (0, 0) = 1 := by
  simp [blockBeam]

example (n : ℕ) (eta : ℝ) : jointMix n eta (0 : FockKernel n) (vacuum n) = 0 := by
  funext a b
  simp [jointMix, productCoeff]

example {n : ℕ} (i : Fin n) : modeEnergy (0 : FockKernel n) i = 0 := by
  simp [modeEnergy]

example {n : ℕ} (X : FockKernel n) (d : SpectralResolution X) :
    spectralEntropyNats X ≤ ∑' j, ENNReal.ofReal (-(d.weight j : ℝ) * Real.log (d.weight j : ℝ)) :=
  iInf_le _ d

example {n : ℕ} (X : FockKernel n) (h : Gaussian X) : IsDensity X := h.1

example (n : ℕ) : realFockTracePair (0 : FockKernel n) (vacuum n) = 0 := by
  simp [realFockTracePair]

example (n : ℕ) : wehrl (0 : FockKernel n) = 0 := by
  simp [wehrl, husimi]

example (eta : ℝ) : (0, 0) ∈ homodyneRateRegion eta 0 := by
  refine ⟨le_rfl, le_rfl, 0, le_rfl, zero_le_one, ?_, ?_⟩ <;>
    simp

example (eta : ℝ) : (0, 0) ∈ heterodyneRateRegion eta 0 := by
  refine ⟨le_rfl, le_rfl, 0, le_rfl, zero_le_one, ?_, ?_⟩ <;>
    simp

end QAlgorithms.Papers.Independent.Next46.P32


