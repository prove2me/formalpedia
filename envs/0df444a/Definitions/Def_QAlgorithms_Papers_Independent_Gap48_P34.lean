-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P34
-- name    : QAlgorithms_Papers_Independent_Gap48_P34
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:43:26.584987+00:00
-- url     : https://prove2.me/theorems/1d5e731b-e8bf-44e2-a408-9aa738241f1a
-- title:
--   Definitions for Strong converse for the classical capacity of optical quantum communication channels
-- statement:
--   The objects the formalized statements of *Strong converse for the classical capacity of optical quantum communication channels* (arXiv:1401.4161) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ModeState`: PDF pp.6--7: normalized positive trace-class states, with no energy, Gaussianity, diagonality, product-state, or finite-support restriction.
--   - `blockCharacteristic`: PDF p.3, (6): symmetrically ordered full Weyl characteristic function. The displacement is the accepted normal-ordered oscillator displacement, with vacuum characteristic exp(-sum |z_j|^2/2), hence vacuum covariance I.
--   - `OpticalChannel`: PDF pp.3--4, (5)--(7): the actual phase-insensitive CPTP channel and its identical independent block uses. The complete characteristic law on ALL states fixes the block maps, including their action on entangled inputs; this is not a condition only on Gaussian means or covariance matrices. CPTP means linearity on trace class, trace preservation, and positivity of all finite ancillary matrix amplifications. No optimizer fact is assumed.
--   - `noiseEnergy`: PDF p.5, (18): noise photons produced by the vacuum; not a free energy.
--   - `outputEnergy`: PDF p.5, (18): output photons for thermal input of mean NS.
--   - `thermalRenyi`: PDF p.12, (79): exact thermal Renyi entropy. Used only for alpha>1 and x>=0, where (x+1)^alpha-x^alpha is strictly positive.
--   - `renyiV`: PDF p.13, (84): the printed conservative v, not the exact (81). For x>=0, A=(x+1)^(3/2)-x^(3/2)>=1 and 0<B=sqrt(x+1)-sqrt(x)<=1, so A^2+B^(-2)+1 bounds A^(-1)+B^(-1)+1.
--   - `renyiK`: PDF p.13, (87): K depends only on the actual vacuum output energy.
--   - `VanishingTail`: PDF p.7, (31)--(32): a nonnegative decreasing tail tending to zero. No exponential speed or first-moment bound is part of this condition.
--   - `photonCutoff`: PDF p.6, (30): actual finite-rank number projector. Each coordinate is at most L, and the additional total restriction is sum_j a_j<=L. The Hilbert space on which it acts remains the full completed Fock space.
--   - `cutoffMass`: PDF p.7, (33): retained photon mass Tr(Pi_L rho).
--   - `OpticalCode`: PDF pp.6--7,10: positive message count, arbitrary normalized block codewords, and a fixed normalized collective decoding POVM. Messages are uniform. No reference entanglement, feedback, or input-dependent decoder is included.
--   - `successProbability`: PDF p.10, (65): ordinary average decoding success for a uniform message.
--   - `photonOccupationConstraint`: PDF p.7, (32): constraint on the average state, equivalently the average of the retained masses. No messagewise constraint is imposed.
--   - `gentleError`: PDF pp.10,12, (65),(67),(77): the entire loss is under the outer root.
--   - `StrongConverseAt`: PDF pp.2,12: operational strong converse at a specified threshold. Family index k denotes blocklength k+1, thereby including every positive blocklength. Any eventually uniformly above-threshold rate is allowed; codebooks may vary arbitrarily with blocklength and may contain entanglement.
-- source:
--   Strong converse for the classical capacity of optical quantum communication channels, arXiv:1401.4161v3, https://arxiv.org/abs/1401.4161v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

/-!
Bardhan, Garcia-Patron, Wilde and Winter, arXiv:1401.4161v3.
Full oscillator spaces, ordinary unassisted classical codes, and bit entropies.
All local definitions have bodies. No Gaussian optimizer or concentration
conclusion is a field of the channel or code definitions.

Source corrections: Lemma 1 uses ceil(n*(NSprime+s)), following (50)--(59),
rather than the printed ceil(n*NSprime+delta2). Theorem 1 and Corollary 1
absorb photon slack and finite rank overhead into an arbitrary positive entropy
slack; a vanishing remainder is enlarged on a finite initial segment.
The printed conservative K in (84),(87) is retained without the false equality
of (84) with (81). Unconditional exponential decay in the abstract is deferred.
Compilation and independent moderation are pending the pipeline handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P34

open Filter
open scoped BigOperators Topology
open QAlgorithms.Papers.Independent.Renew46.P30
  (HilbertDensity nuclearExpansionTrace mixedLikelihood
   TraceClassCPTP multiKet multiDisplacement)
open QAlgorithms.Papers.Independent.Claimed50.P30 (ModeOperator)
open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)
open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)
open QAlgorithms.Papers.Independent.Claimed50.P08 (codeRate)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.6--7: normalized positive trace-class states, with no energy,
Gaussianity, diagonality, product-state, or finite-support restriction. -/
abbrev ModeState (n : ℕ) := {rho : ModeOperator n // HilbertDensity rho}

/-- PDF p.3, (6): symmetrically ordered full Weyl characteristic function.
The displacement is the accepted normal-ordered oscillator displacement,
with vacuum characteristic exp(-sum |z_j|^2/2), hence vacuum covariance I. -/
def blockCharacteristic {n : ℕ} (rho : ModeOperator n) (z : Fin n → ℂ) : ℂ :=
  nuclearExpansionTrace (rho.comp (multiDisplacement z))

/-- PDF pp.3--4, (5)--(7): the actual phase-insensitive CPTP channel and
its identical independent block uses. The complete characteristic law on ALL
states fixes the block maps, including their action on entangled inputs;
this is not a condition only on Gaussian means or covariance matrices.
CPTP means linearity on trace class, trace preservation, and positivity of
all finite ancillary matrix amplifications. No optimizer fact is assumed. -/
structure OpticalChannel where
  tau : ℝ
  nu : ℝ
  tau_nonneg : 0 ≤ tau
  noise_valid : |tau - 1| ≤ nu
  block : ∀ n : ℕ, ModeOperator n → ModeOperator n
  block_cptp : ∀ n, TraceClassCPTP (block n)
  characteristic_law : ∀ n (rho : ModeState n) (z : Fin n → ℂ),
    blockCharacteristic (block n rho.val) z =
      blockCharacteristic rho.val (fun j => (Real.sqrt tau : ℂ) * z j) *
        (Real.exp (-nu * (∑ j, Complex.normSq (z j)) / 2) : ℂ)

/-- PDF p.5, (18): noise photons produced by the vacuum; not a free energy. -/
def noiseEnergy (P : OpticalChannel) : ℝ := (P.tau + P.nu - 1) / 2

/-- PDF p.5, (18): output photons for thermal input of mean NS. -/
def outputEnergy (P : OpticalChannel) (NS : ℝ) : ℝ := P.tau * NS + noiseEnergy P

/-- PDF p.12, (79): exact thermal Renyi entropy. Used only for alpha>1
and x>=0, where (x+1)^alpha-x^alpha is strictly positive. -/
def thermalRenyi (alpha x : ℝ) : ℝ :=
  logBits ((x + 1) ^ alpha - x ^ alpha) / (alpha - 1)

/-- PDF p.13, (84): the printed conservative v, not the exact (81).
For x>=0, A=(x+1)^(3/2)-x^(3/2)>=1 and
0<B=sqrt(x+1)-sqrt(x)<=1, so A^2+B^(-2)+1 bounds A^(-1)+B^(-1)+1. -/
def renyiV (x : ℝ) : ℝ :=
  ((x + 1) ^ (3 / 2 : ℝ) - x ^ (3 / 2 : ℝ)) ^ (2 : ℕ) +
    ((Real.sqrt (x + 1) - Real.sqrt x) ^ (2 : ℕ))⁻¹ + 1

/-- PDF p.13, (87): K depends only on the actual vacuum output energy. -/
def renyiK (x : ℝ) : ℝ := 4 * (logBits (renyiV x)) ^ (2 : ℕ)

/-- PDF p.7, (31)--(32): a nonnegative decreasing tail tending to zero.
No exponential speed or first-moment bound is part of this condition. -/
def VanishingTail (delta : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ delta n) ∧ Antitone delta ∧ Tendsto delta atTop (nhds 0)

/-- PDF p.6, (30): actual finite-rank number projector. Each coordinate
is at most L, and the additional total restriction is sum_j a_j<=L.
The Hilbert space on which it acts remains the full completed Fock space. -/
def photonCutoff (n L : ℕ) : ModeOperator n :=
  ∑ a : Fin n → Fin (L + 1),
    if (∑ j, (a j).val) ≤ L then
      InnerProductSpace.rankOne ℂ (multiKet (fun j => (a j).val))
        (multiKet (fun j => (a j).val))
    else 0

/-- PDF p.7, (33): retained photon mass Tr(Pi_L rho). -/
def cutoffMass {n : ℕ} (rho : ModeOperator n) (L : ℕ) : ℝ :=
  mixedLikelihood (photonCutoff n L) rho

/-- PDF pp.6--7,10: positive message count, arbitrary normalized block
codewords, and a fixed normalized collective decoding POVM. Messages are uniform.
No reference entanglement, feedback, or input-dependent decoder is included. -/
structure OpticalCode (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encoder : Fin messages → ModeState n
  decoder : Fin messages → ModeOperator n
  decoder_positive : ∀ m, ContinuousLinearMap.IsPositive (decoder m)
  decoder_complete : (∑ m, decoder m) = 1

/-- PDF p.12: use the imported scalar codeRate with d=messages-1.
The positive message count guarantees d+1=messages, so this is log2(M)/n. -/
example {n : ℕ} (C : OpticalCode n) : C.messages - 1 + 1 = C.messages := by
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt C.messages_pos)

/-- PDF p.10, (65): ordinary average decoding success for a uniform message. -/
def successProbability (P : OpticalChannel) {n : ℕ} (C : OpticalCode n) : ℝ :=
  (∑ m, mixedLikelihood (C.decoder m) (P.block n (C.encoder m).val)) /
    (C.messages : ℝ)

/-- PDF p.7, (32): constraint on the average state, equivalently the
average of the retained masses. No messagewise constraint is imposed. -/
def photonOccupationConstraint {n : ℕ} (C : OpticalCode n) (NS delta : ℝ) : Prop :=
  1 - delta ≤ (∑ m, cutoffMass (C.encoder m).val ⌈(n : ℝ) * NS⌉₊) /
    (C.messages : ℝ)

/-- PDF pp.10,12, (65),(67),(77): the entire loss is under the outer root. -/
def gentleError (delta1 delta3 : ℝ) : ℝ :=
  2 * Real.sqrt (delta1 + 2 * Real.sqrt delta1 + delta3)

/-- PDF pp.2,12: operational strong converse at a specified threshold.
Family index k denotes blocklength k+1, thereby including every positive
blocklength. Any eventually uniformly above-threshold rate is allowed;
codebooks may vary arbitrarily with blocklength and may contain entanglement. -/
def StrongConverseAt (P : OpticalChannel) (NS threshold : ℝ) : Prop :=
  ∀ (codes : ∀ k : ℕ, OpticalCode (k + 1)) (delta1 : ℕ → ℝ),
    VanishingTail delta1 →
    (∀ k, photonOccupationConstraint (codes k) NS (delta1 (k + 1))) →
    ∀ R : ℝ, threshold < R →
      (∀ᶠ k in atTop, R ≤ codeRate ((codes k).messages - 1) (k + 1)) →
      Tendsto (fun k => successProbability P (codes k)) atTop (nhds 0)

/-- Sanity: vacuum entropy is zero with the continuous 0 log 0 convention. -/
example : thermalEntropy 0 = 0 := by
  simp [thermalEntropy]

/-- Sanity: zero input/output tail has no gentle-measurement error. -/
example : gentleError 0 0 = 0 := by
  norm_num [gentleError]

/-- Sanity: the identity-channel parameters produce no vacuum noise. -/
example (P : OpticalChannel) (ht : P.tau = 1) (hn : P.nu = 0) (NS : ℝ) :
    outputEnergy P NS = NS := by
  simp [outputEnergy, noiseEnergy, ht, hn]

/-- Sanity: the cutoff sum has the actual vacuum dyad when L=0;
Fin 1 has a unique value, and all n coordinates are consequently zero. -/
example (n : ℕ) : photonCutoff n 0 =
    InnerProductSpace.rankOne ℂ (multiKet (0 : Fin n → ℕ)) (multiKet (0 : Fin n → ℕ)) := by
  simp [photonCutoff] <;> rfl

end QAlgorithms.Papers.Independent.Gap48.P34


