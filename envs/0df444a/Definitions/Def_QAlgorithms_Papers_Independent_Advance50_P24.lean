-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P24
-- name    : QAlgorithms_Papers_Independent_Advance50_P24
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T12:55:50.58398+00:00
-- url     : https://prove2.me/theorems/8b2de2ae-07ca-4242-8801-2f0e4a412d71
-- title:
--   Definitions for Private-Capacity Bounds for Bosonic Wiretap Channels
-- statement:
--   The objects the formalized statements of *Private-Capacity Bounds for Bosonic Wiretap Channels* (arXiv:1202.1126) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `singleCapacity`: PDF pp.1--2, (1)--(2),(8): width one, arbitrary mixed block states, collective normalized POVMs, private randomization, and codebook-average energy.
--   - `lowerBound`: PDF p.1, (4): continuous vacuum extension through the accepted g(0)=0.
--   - `upperBound`: PDF p.2, (9), including the antidegradable and vacuum branches.
--   - `linearEntropyCoefficient`: PDF p.2, (22): x(1-log x), continuously extended to zero, without 1/0.
--   - `singleRemainder`: PDF p.2, (21): the remainder is computed from the capacity. All theorems taking toReal also conclude that the capacity is finite.
--   - `photonBudgetAllocations`: PDF pp.3--4, (25),(32)--(34): nonnegative photon allocations with exact total N.
--   - `transmissivityCube`: PDF pp.3--5: the complete domain of finite transmissivity vectors.
--   - `allocationSup`: PDF pp.4--5, corrected (49): supremum of the SUM of scalar bounds. On m>0,N>=0 the theorems below conclude attainment, so the real supremum is used only on its nonempty bounded domain. Outside that domain no claim is made.
--   - `parallelLower`: PDF p.5, (49)--(53): the missing printed summation is restored.
--   - `parallelUpper`: PDF p.4, following (42): independently optimized upper bound.
--   - `allocatedPrivateSup`: PDF p.5, corrected (45): the mean-instantaneous expression uses this extended allocation supremum. This is not defined to be an operational fading capacity.
--   - `parallelBeam`: PDF p.3, (25): n uses of m independently acting beam splitters. The mode of flattened index i is (finProdFinEquiv.symm i).2. The minus sign on the vacuum-to-Eve coefficient is in beamCoefficient.
--   - `parallelBroadcast`: PDF p.3, (25): the full common vacuum dilation. X may have arbitrary correlations across all modes and uses; it is not restricted to product or Gaussian states. Physical uses below supply normalized density kernels via BosonicPrivateCode.
--   - `parallelEveMessage`: PDF pp.1,4: first average private randomization in each Eve MESSAGE state.
--   - `parallelEveAverage`: PDF pp.1,4: uniform secret-message mixture at the entire Eve output.
--   - `parallelLeakage`: PDF pp.1,4: message Holevo leakage in nats, after private randomization. Finite average photon energy on the theorem domain ensures finite entropies, as for the accepted single-mode interface; no cutoff is imposed.
--   - `parallelDecodes`: PDF pp.1,4: the same branchwise reliability convention as the accepted single-mode capacity; each decoder is a normalized collective Fock POVM.
--   - `parallelAchievable`: PDF p.4, (32)--(34): unrestricted operational rates per m-mode use. The TOTAL photon budget is n*N, averaged over messages and random seeds. There is no per-mode, per-message, or per-use cap in the code constraint.
--   - `parallelPrivateCapacityNats`: PDF p.4, (34): genuine heterogeneous parallel-channel operational capacity. The ENNReal supremum retains empty/unbounded semantics and contains no additivity claim.
--   - `aliceBobBlock`: PDF p.3, (23)--(24): Alice-to-Bob block, with the first m input ports and the first k output ports. Rectangular dimensions are retained.
--   - `aliceBobGram`: PDF pp.3,5: actual Hermitian Gram matrix, never the transposed index typo t_ba.
--   - `gramSpectrum`: PDF pp.3,5: the spectrum is computed from the block, with multiplicities.
--   - `unitaryBasisDiagonal`: PDF p.5: real diagonal in a chosen orthonormal input basis.
--   - `inputOccupation`: PDF p.3, (23): Alice occupies the first m ports, with all others vacuum. The use index and mode index are converted by the same finProdFinEquiv as above.
--   - `joinedOutputOccupation`: PDF p.3, (23): join Bob and Eve occupations within one channel use.
--   - `passiveIsometry`: PDF p.3, (23)--(24): full passive vacuum isometry coefficients. The accepted passiveEntry is the exact finite number-sector creation-polynomial formula for a general complex mode matrix. No bounded-operator fallback is used.
--   - `passiveBroadcast`: PDF p.3, (23): joint Bob/Eve density coefficients of n uses of the specified complex unitary and vacuum ancillary ports. X is an arbitrary full input kernel; operational codes supply normalized mixed density operators.
--   - `PassivePrivateCode`: PDF pp.3--4: total mean-photon wiretap code for rectangular Bob outputs. Only the decoder basis dimension differs from the accepted BosonicPrivateCode.
--   - `passiveCodeEnergy`: PDF pp.1,3--4, (2),(32): unconditional block energy, never per-message.
--   - `passiveEveMessage`: PDF pp.1,3--4: Eve receives all l complementary modes; average private randomization before message Holevo information is evaluated.
--   - `passiveEveAverage`: PDF pp.1,3--4: Eve's unconditional normalized message mixture.
--   - `passiveLeakage`: PDF pp.1,3--4: nats-valued message Holevo leakage for the actual complement.
--   - `passiveDecodes`: PDF pp.1,3--4: accepted reliability convention on the full k-mode Bob output.
--   - `passiveAchievable`: PDF pp.3--4, (32): true operational rates for the general passive channel. The matrix is fixed across n uses; energy is averaged over the entire codebook.
--   - `passiveCapacity`: PDF pp.3--4: general-channel operational private capacity, not a spectral formula, restricted to actual unitary and feasible dimensions in all theorems.
--   - `largestTransmissivity`: PDF p.4, (43): largest eigenvalue, with a nonempty finite spectrum.
--   - `passiveRemainder`: PDF p.4, (43): computed general-channel remainder, not freely chosen data. The printed signed coefficient is replaced by its positive part: Theorems 1,4 give zero capacity when every transmissivity is at most 1/2.
-- source:
--   Private-Capacity Bounds for Bosonic Wiretap Channels, arXiv:1202.1126v1, https://arxiv.org/abs/1202.1126v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

/-!
Wang--Shapiro--Chandrasekaran--Wornell, arXiv:1202.1126v1.
Rates and entropies are in nats. The accepted full-Fock, message-Holevo
private capacity is used unconditionally. Heterogeneous parallel channels
below are actual tensor products of vacuum beam splitters, not a capacity
formula adopted as a definition. The general rectangular channel is constructed from the accepted passiveEntry.
Its full physical equivalence theorem and the operational fading model are
deferred; see HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P24

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ComplexOrder Matrix.Norms.Elementwise
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Support50.P06
  (BosonicPrivateCode randomizedPrivateCodePhotonBudget
   holevoMessagePrivacyCapacityNats)
open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel beamCoefficient vacuum bobMarginal charlieMarginal
   spectralEntropyNats realFockTracePair)
open QAlgorithms.Papers.Independent.Dependency50.P16 (majorizedBy)
open QAlgorithms.Papers.Independent.Renew46.P30 (passiveEntry)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Next46.P32 (FockPOVM)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1--2, (1)--(2),(8): width one, arbitrary mixed block states,
collective normalized POVMs, private randomization, and codebook-average energy. -/
abbrev singleCapacity (eta N : ℝ) : ℝ≥0∞ :=
  holevoMessagePrivacyCapacityNats 1 eta N false

/-- PDF p.1, (4): continuous vacuum extension through the accepted g(0)=0. -/
def lowerBound (eta N : ℝ) : ℝ :=
  if 1 / 2 < eta then g (eta * N) - g ((1 - eta) * N) else 0

/-- PDF p.2, (9), including the antidegradable and vacuum branches. -/
def upperBound (eta N : ℝ) : ℝ :=
  if 1 / 2 < eta then g ((2 * eta - 1) * N) else 0

/-- PDF p.2, (22): x(1-log x), continuously extended to zero, without 1/0. -/
def linearEntropyCoefficient (x : ℝ) : ℝ := x - x * Real.log x

/-- PDF p.2, (21): the remainder is computed from the capacity.
All theorems taking toReal also conclude that the capacity is finite. -/
def singleRemainder (eta N : ℝ) : ℝ :=
  (singleCapacity eta N).toReal - (2 * eta - 1) * N * Real.log (1 / N)

/-- PDF pp.3--4, (25),(32)--(34): nonnegative photon allocations with exact total N. -/
def photonBudgetAllocations (m : ℕ) (N : ℝ) : Set (Fin m → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = N}

/-- PDF pp.3--5: the complete domain of finite transmissivity vectors. -/
def transmissivityCube (m : ℕ) : Set (Fin m → ℝ) :=
  {eta | ∀ i, eta i ∈ Set.Icc (0 : ℝ) 1}

/-- PDF pp.4--5, corrected (49): supremum of the SUM of scalar bounds.
On m>0,N>=0 the theorems below conclude attainment, so the real supremum
is used only on its nonempty bounded domain. Outside that domain no claim is made. -/
def allocationSup {m : ℕ} (f : ℝ → ℝ → ℝ) (eta : Fin m → ℝ) (N : ℝ) : ℝ :=
  sSup {r | ∃ a ∈ photonBudgetAllocations m N, r = ∑ i, f (eta i) (a i)}

/-- PDF p.5, (49)--(53): the missing printed summation is restored. -/
abbrev parallelLower {m : ℕ} (eta : Fin m → ℝ) (N : ℝ) : ℝ :=
  allocationSup lowerBound eta N

/-- PDF p.4, following (42): independently optimized upper bound. -/
abbrev parallelUpper {m : ℕ} (eta : Fin m → ℝ) (N : ℝ) : ℝ :=
  allocationSup upperBound eta N

/-- PDF p.5, corrected (45): the mean-instantaneous expression uses this
extended allocation supremum. This is not defined to be an operational fading capacity. -/
def allocatedPrivateSup {m : ℕ} (eta : Fin m → ℝ) (N : ℝ) : ℝ≥0∞ :=
  sSup {r | ∃ a ∈ photonBudgetAllocations m N, r = ∑ i, singleCapacity (eta i) (a i)}

/-- PDF p.3, (25): n uses of m independently acting beam splitters.
The mode of flattened index i is (finProdFinEquiv.symm i).2.
The minus sign on the vacuum-to-Eve coefficient is in beamCoefficient. -/
def parallelBeam {m : ℕ} (eta : Fin m → ℝ) (n : ℕ)
    (out inp : NumberString (n * m) × NumberString (n * m)) : ℂ :=
  ((∏ i : Fin (n * m), beamCoefficient
    (eta (finProdFinEquiv.symm i).2)
    (out.1 i) (out.2 i) (inp.1 i) (inp.2 i) : ℝ) : ℂ)

/-- PDF p.3, (25): the full common vacuum dilation. X may have arbitrary
correlations across all modes and uses; it is not restricted to product or Gaussian states.
Physical uses below supply normalized density kernels via BosonicPrivateCode. -/
def parallelBroadcast {m : ℕ} (eta : Fin m → ℝ) (n : ℕ)
    (X : FockKernel (n * m)) :
    Matrix (NumberString (n * m) × NumberString (n * m))
      (NumberString (n * m) × NumberString (n * m)) ℂ :=
  fun u v => ∑' a : NumberString (n * m) × NumberString (n * m),
    ∑' b : NumberString (n * m) × NumberString (n * m),
      parallelBeam eta n u a * X a.1 b.1 * vacuum (n * m) a.2 b.2 *
        star (parallelBeam eta n v b)

/-- PDF pp.1,4: first average private randomization in each Eve MESSAGE state. -/
def parallelEveMessage {m n M : ℕ} (eta : Fin m → ℝ)
    (C : BosonicPrivateCode (n * m) M) (j : Fin M) : FockKernel (n * m) :=
  fun a b => ∑' k : ℕ, (C.randomWeight k : ℂ) *
    charlieMarginal (parallelBroadcast eta n (C.encoder j k).coefficients) a b

/-- PDF pp.1,4: uniform secret-message mixture at the entire Eve output. -/
def parallelEveAverage {m n M : ℕ} (eta : Fin m → ℝ)
    (C : BosonicPrivateCode (n * m) M) : FockKernel (n * m) :=
  fun a b => (M : ℂ)⁻¹ * ∑ j : Fin M, parallelEveMessage eta C j a b

/-- PDF pp.1,4: message Holevo leakage in nats, after private randomization.
Finite average photon energy on the theorem domain ensures finite entropies,
as for the accepted single-mode interface; no cutoff is imposed. -/
def parallelLeakage {m n M : ℕ} (eta : Fin m → ℝ)
    (C : BosonicPrivateCode (n * m) M) : ℝ≥0∞ :=
  spectralEntropyNats (parallelEveAverage eta C) -
    (M : ℝ≥0∞)⁻¹ * ∑ j : Fin M, spectralEntropyNats (parallelEveMessage eta C j)

/-- PDF pp.1,4: the same branchwise reliability convention as the accepted
single-mode capacity; each decoder is a normalized collective Fock POVM. -/
def parallelDecodes {m n M : ℕ} (eta : Fin m → ℝ)
    (C : BosonicPrivateCode (n * m) M) (epsilon : ℝ) : Prop :=
  ∀ (j : Fin M) (k : ℕ), 1 - epsilon <
    realFockTracePair
      (bobMarginal (parallelBroadcast eta n (C.encoder j k).coefficients))
      (C.decoder.effect j)

/-- PDF p.4, (32)--(34): unrestricted operational rates per m-mode use.
The TOTAL photon budget is n*N, averaged over messages and random seeds.
There is no per-mode, per-message, or per-use cap in the code constraint. -/
def parallelAchievable {m : ℕ} (eta : Fin m → ℝ) (N R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ M : ℕ, ∃ C : BosonicPrivateCode (n * m) M,
        randomizedPrivateCodePhotonBudget C ≤ ENNReal.ofReal ((n : ℝ) * N) ∧
        parallelDecodes eta C epsilon ∧
        parallelLeakage eta C ≤ ENNReal.ofReal epsilon ∧
        R - delta ≤ Real.log (M : ℝ) / (n : ℝ)

/-- PDF p.4, (34): genuine heterogeneous parallel-channel operational capacity.
The ENNReal supremum retains empty/unbounded semantics and contains no additivity claim. -/
def parallelPrivateCapacityNats {m : ℕ} (eta : Fin m → ℝ) (N : ℝ) : ℝ≥0∞ :=
  sSup {r | ∃ R : ℝ, parallelAchievable eta N R ∧ r = ENNReal.ofReal R}

/-- PDF p.3, (23)--(24): Alice-to-Bob block, with the first m input ports
and the first k output ports. Rectangular dimensions are retained. -/
def aliceBobBlock {m k l : ℕ} (hm : m ≤ k + l)
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) : Matrix (Fin k) (Fin m) ℂ :=
  fun i j => t (Fin.castAdd l i) (Fin.castLE hm j)

/-- PDF pp.3,5: actual Hermitian Gram matrix, never the transposed index typo t_ba. -/
def aliceBobGram {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ := A.conjTranspose * A

/-- PDF pp.3,5: the spectrum is computed from the block, with multiplicities. -/
def gramSpectrum {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℂ) : Fin m → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues

/-- PDF p.5: real diagonal in a chosen orthonormal input basis. -/
def unitaryBasisDiagonal {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix.unitaryGroup (Fin m) ℂ) : Fin m → ℝ :=
  fun i => (((U : Matrix (Fin m) (Fin m) ℂ).conjTranspose * A *
    (U : Matrix (Fin m) (Fin m) ℂ)) i i).re

/-- PDF p.3, (23): Alice occupies the first m ports, with all others vacuum.
The use index and mode index are converted by the same finProdFinEquiv as above. -/
def inputOccupation {m n d : ℕ} (a : NumberString (n * m)) (u : Fin n)
    (j : Fin d) : ℕ :=
  if h : j.val < m then a (finProdFinEquiv (u, ⟨j.val, h⟩)) else 0

/-- PDF p.3, (23): join Bob and Eve occupations within one channel use. -/
def joinedOutputOccupation {k l n : ℕ}
    (q : NumberString (n * k) × NumberString (n * l)) (u : Fin n)
    (j : Fin (k + l)) : ℕ :=
  if h : j.val < k then q.1 (finProdFinEquiv (u, ⟨j.val, h⟩))
  else q.2 (finProdFinEquiv (u, ⟨j.val - k, by omega⟩))

/-- PDF p.3, (23)--(24): full passive vacuum isometry coefficients.
The accepted passiveEntry is the exact finite number-sector creation-polynomial
formula for a general complex mode matrix. No bounded-operator fallback is used. -/
def passiveIsometry {m k l : ℕ}
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) (n : ℕ)
    (q : NumberString (n * k) × NumberString (n * l))
    (a : NumberString (n * m)) : ℂ :=
  ∏ u : Fin n, passiveEntry t (joinedOutputOccupation q u) (inputOccupation a u)

/-- PDF p.3, (23): joint Bob/Eve density coefficients of n uses of the
specified complex unitary and vacuum ancillary ports. X is an arbitrary full
input kernel; operational codes supply normalized mixed density operators. -/
def passiveBroadcast {m k l : ℕ}
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) (n : ℕ)
    (X : FockKernel (n * m)) :
    Matrix (NumberString (n * k) × NumberString (n * l))
      (NumberString (n * k) × NumberString (n * l)) ℂ :=
  fun q r => ∑' a : NumberString (n * m), ∑' b : NumberString (n * m),
    passiveIsometry t n q a * X a b * star (passiveIsometry t n r b)

/-- PDF pp.3--4: total mean-photon wiretap code for rectangular Bob outputs.
Only the decoder basis dimension differs from the accepted BosonicPrivateCode. -/
structure PassivePrivateCode (m k n M : ℕ) where
  block_positive : 0 < n
  messages_positive : 0 < M
  randomWeight : ℕ → ℝ
  random_nonnegative : ∀ r, 0 ≤ randomWeight r
  random_summable : Summable randomWeight
  random_total : (∑' r, randomWeight r) = 1
  encoder : Fin M → ℕ → State (NumberString (n * m))
  decoder : FockPOVM (NumberString (n * k)) (Fin M)

/-- PDF pp.1,3--4, (2),(32): unconditional block energy, never per-message. -/
def passiveCodeEnergy {m k n M : ℕ} (C : PassivePrivateCode m k n M) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ j : Fin M, ∑' r : ℕ,
    ENNReal.ofReal (C.randomWeight r) *
      QAlgorithms.Papers.Independent.Support50.P06.totalEnergy (C.encoder j r).coefficients

/-- PDF pp.1,3--4: Eve receives all l complementary modes; average private
randomization before message Holevo information is evaluated. -/
def passiveEveMessage {m k l n M : ℕ}
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ)
    (C : PassivePrivateCode m k n M) (j : Fin M) : FockKernel (n * l) :=
  fun a b => ∑' r : ℕ, (C.randomWeight r : ℂ) *
    ∑' q : NumberString (n * k),
      passiveBroadcast t n (C.encoder j r).coefficients (q, a) (q, b)

/-- PDF pp.1,3--4: Eve's unconditional normalized message mixture. -/
def passiveEveAverage {m k l n M : ℕ}
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ)
    (C : PassivePrivateCode m k n M) : FockKernel (n * l) :=
  fun a b => (M : ℂ)⁻¹ * ∑ j : Fin M, passiveEveMessage t C j a b

/-- PDF pp.1,3--4: nats-valued message Holevo leakage for the actual complement. -/
def passiveLeakage {m k l n M : ℕ}
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ)
    (C : PassivePrivateCode m k n M) : ℝ≥0∞ :=
  spectralEntropyNats (passiveEveAverage t C) -
    (M : ℝ≥0∞)⁻¹ * ∑ j : Fin M, spectralEntropyNats (passiveEveMessage t C j)

/-- PDF pp.1,3--4: accepted reliability convention on the full k-mode Bob output. -/
def passiveDecodes {m k l n M : ℕ}
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ)
    (C : PassivePrivateCode m k n M) (epsilon : ℝ) : Prop :=
  ∀ (j : Fin M) (r : ℕ), 1 - epsilon <
    realFockTracePair
      (fun a b => ∑' e : NumberString (n * l),
        passiveBroadcast t n (C.encoder j r).coefficients (a, e) (b, e))
      (C.decoder.effect j)

/-- PDF pp.3--4, (32): true operational rates for the general passive channel.
The matrix is fixed across n uses; energy is averaged over the entire codebook. -/
def passiveAchievable (m k l : ℕ)
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) (N R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ M : ℕ, ∃ C : PassivePrivateCode m k n M,
        passiveCodeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * N) ∧
        passiveDecodes t C epsilon ∧ passiveLeakage t C ≤ ENNReal.ofReal epsilon ∧
        R - delta ≤ Real.log (M : ℝ) / (n : ℝ)

/-- PDF pp.3--4: general-channel operational private capacity, not a spectral
formula, restricted to actual unitary and feasible dimensions in all theorems. -/
def passiveCapacity (m k l : ℕ)
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) (N : ℝ) : ℝ≥0∞ :=
  sSup {r | ∃ R : ℝ, passiveAchievable m k l t N R ∧ r = ENNReal.ofReal R}

/-- PDF p.4, (43): largest eigenvalue, with a nonempty finite spectrum. -/
def largestTransmissivity {m k : ℕ} (hm : 0 < m)
    (A : Matrix (Fin k) (Fin m) ℂ) : ℝ :=
  Finset.univ.sup' (by exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩) (gramSpectrum A)

/-- PDF p.4, (43): computed general-channel remainder, not freely chosen data.
The printed signed coefficient is replaced by its positive part: Theorems 1,4
give zero capacity when every transmissivity is at most 1/2. -/
def passiveRemainder (m k l : ℕ) (hm : 0 < m) (hdim : m ≤ k + l)
    (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) (N : ℝ) : ℝ :=
  (passiveCapacity m k l t N).toReal -
    max 0 (2 * largestTransmissivity hm (aliceBobBlock hdim t) - 1) * N * Real.log (1 / N)

example {m k l : ℕ} (t : Matrix (Fin (k + l)) (Fin (k + l)) ℂ)
    (q : NumberString (0 * k) × NumberString (0 * l))
    (a : NumberString (0 * m)) : passiveIsometry t 0 q a = 1 := by
  simp [passiveIsometry]

example (N : ℝ) : lowerBound (1 / 2) N = 0 := by
  simp [lowerBound]

example : linearEntropyCoefficient 0 = 0 := by
  simp [linearEntropyCoefficient]

example (eta : ℝ) : upperBound eta 0 = 0 := by
  simp [upperBound, g]

example (m : ℕ) : (fun _ : Fin m => (0 : ℝ)) ∈ photonBudgetAllocations m 0 := by
  simp [photonBudgetAllocations]

example {m : ℕ} (eta : Fin m → ℝ)
    (out inp : NumberString (0 * m) × NumberString (0 * m)) :
    parallelBeam eta 0 out inp = 1 := by
  haveI : IsEmpty (Fin (0 * m)) := by
    simpa only [Nat.zero_mul] using (inferInstance : IsEmpty (Fin 0))
  simp [parallelBeam]

example {m k : ℕ} (A : Matrix (Fin k) (Fin m) ℂ) :
    (aliceBobGram A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A

example : (fun _ : Fin 1 => (0 : ℝ)) ∈ transmissivityCube 1 := by
  simp [transmissivityCube]

example (N : ℝ) (hN : 0 < N) (eta : Fin 0 → ℝ) :
    allocatedPrivateSup eta N = 0 := by
  simp [allocatedPrivateSup, photonBudgetAllocations, ne_of_lt hN]

example (N : ℝ) (hN : 0 < N) (eta : Fin 0 → ℝ) :
    allocationSup lowerBound eta N = 0 := by
  simp [allocationSup, photonBudgetAllocations, ne_of_lt hN]

example {m k l : ℕ} (hm : m ≤ k + l) :
    aliceBobBlock hm (0 : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) = 0 := by
  rfl

example {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    unitaryBasisDiagonal A 1 = fun i => (A i i).re := by
  funext i
  simp [unitaryBasisDiagonal]

example : parallelBeam (fun _ : Fin 1 => (1 : ℝ)) 1
    ((fun _ => 1), (fun _ => 0)) ((fun _ => 1), (fun _ => 0)) = 1 := by
  norm_num [parallelBeam, beamCoefficient, Fin.prod_univ_succ, Finset.sum_range_succ]

example : parallelBeam (fun _ : Fin 1 => (0 : ℝ)) 1
    ((fun _ => 0), (fun _ => 1)) ((fun _ => 1), (fun _ => 0)) = 1 := by
  norm_num [parallelBeam, beamCoefficient, Fin.prod_univ_succ, Finset.sum_range_succ]

example : parallelBeam (fun _ : Fin 1 => (1 : ℝ)) 1
    ((fun _ => 0), (fun _ => 1)) ((fun _ => 0), (fun _ => 1)) = -1 := by
  norm_num [parallelBeam, beamCoefficient, Fin.prod_univ_succ, Finset.sum_range_succ]

example {m n d : ℕ} (u : Fin n) (j : Fin d) :
    inputOccupation (0 : NumberString (n * m)) u j = 0 := by
  simp [inputOccupation]

example {m k n : ℕ} (C : PassivePrivateCode m k n 1)
    (a b : NumberString (n * k)) :
    C.decoder.effect 0 a b = if a = b then 1 else 0 := by
  by_cases hab : a = b <;> simpa [hab] using C.decoder.complete a b

end QAlgorithms.Papers.Independent.Advance50.P24


