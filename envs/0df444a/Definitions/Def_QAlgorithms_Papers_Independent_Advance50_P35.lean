-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35
-- name    : QAlgorithms_Papers_Independent_Advance50_P35
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:39:16.191026+00:00
-- url     : https://prove2.me/theorems/cac72b96-72fa-4fcf-b61a-36d6909b1c72
-- title:
--   Definitions for Quantum Reading Capacity
-- statement:
--   The objects the formalized statements of *Quantum Reading Capacity* (arXiv:1107.3500) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TensorCopyBasis`: PDF pp.3--4: basis labels for s copies of the COMMON system, including s=0.
--   - `AssistedRegister`: PDF pp.4,8: arbitrary reference Hilbert space, independent of the signal space.
--   - `CellRegister`: PDF pp.4--5: for optical memories, both signal and reference modes are bosonic.
--   - `Memory`: PDF pp.3,8: a finite nonempty ensemble of pairwise distinct CPTP channels. Distinctness is on states, so irrelevant extensions off trace class cannot count.
--   - `traceClassChannelCopies`: PDF pp.3--4,8, (5),(43): tensor power on every block of an entangled input. The recursive slices are trace class on physical inputs; references are untouched.
--   - `cellOutput`: PDF p.8, (43): channel on the signal tensor factors only.
--   - `finiteMemoryHolevoBits`: PDF p.8, (44): chi in bits, using its relative-entropy formula. Zero priors contribute zero even if the corresponding relative entropy is infinite. For normalized finite ensembles this number is finite and bounded by H(prior).
--   - `transmitterInformation`: PDF p.8: conditional information of the one-cell transmitter.
--   - `memoryEntropy`: PDF p.9, (48): marginal Shannon entropy, in bits, with 0 log 0=0.
--   - `unconstrainedCapacity`: PDF pp.8--9, (46): unconstrained optimal VALUE, not an assumed maximum.
--   - `pureUnassistedValue`: PDF p.9, (47): pure, unassisted fixed-s optimal value.
--   - `pureRegisterValue`: PDF pp.9,14: pure-input optimal value on fixed signal/reference registers.
--   - `signalEnergy`: PDF p.4: exact extended mean photon number of the SUM of signal modes. The extended sum records infinite energy instead of silently returning zero.
--   - `cellTotalPhotonEnergy`: PDF pp.13--14, endnote [31]: frozen total photon expectation, with signal modes first and reference modes last in the combined full-Fock register.
--   - `PureClass`: PDF p.9: an energy-INDEPENDENT class of normalized pure inputs on each register.
--   - `MixtureOf`: PDF p.9, (52), interpreted by (56): arbitrary Borel probability mixtures on the SAME registers; component energies need not equal the barycenter energy.
--   - `pureClassCapacity`: PDF p.9, (54): exact-energy pure-class optimum; the supremum is extended.
--   - `mixtureClassCapacity`: PDF p.9, (53): exact AVERAGE energy in the arbitrary-mixture class.
--   - `EnergyFeasible`: PDF p.9: implicit feasibility of pure-class optimization on its energy domain.
--   - `LossMemory`: PDF pp.5,10: binary pure-loss memory; the arbitrary prior includes endpoints.
--   - `vacuumLossAction`: PDF p.5, (13): the frozen full-Fock vacuum attenuator, reindexed from one-mode words to natural photon labels. The environment bypasses readout.
--   - `lossPrior`: PDF pp.5,10: fixed binary priors, independent of every transmitter optimization.
--   - `lossInformation`: PDF pp.8,10: conditional Holevo information for the actual loss-channel outputs.
--   - `coherentAmplitude`: PDF pp.5,10: all coherent product kets, in the full number basis.
--   - `coherentProductProjector`: PDF p.10, (68): coherent projector from its actual ket coefficients.
--   - `IsClassicalCellTransmitter`: PDF pp.5--6, (19)--(22): ALL probability mixtures of coherent products. The measure may be singular, atomic or continuous; no positive density is required. Every coefficient is integrable, preventing a default-zero barycenter integral.
--   - `quantumReadingCapacity`: PDF p.9, (51): quantum capacity at exact TOTAL signal energy n per cell.
--   - `classicalReadingCapacity`: PDF p.10, (65): independently defined classical optimization, not H(xi).
--   - `classicalTotalCapacity`: PDF pp.13--14: independently optimized capacity under the stronger constraint.
--   - `classicalEigenvalue`: PDF p.10, (67): the larger eigenvalue, including arbitrary endpoint priors.
--   - `classicalFormula`: PDF p.10, (66): the scalar expression asserted EQUAL to the optimized capacity.
--   - `coherentInput`: PDF p.10, (72): one signal, no reference, amplitude sqrt(n).
--   - `classicalSingleRate`: PDF pp.6,11, (24)--(25): source-defined classical error-entropy rate. This expression is not the mutual information of every binary measurement.
--   - `eprAmplitude`: PDF pp.6,11--13, (26)--(28): s TMSV pairs, total SIGNAL energy n. Each pair has Schmidt probabilities (n/s)^m/(1+n/s)^(m+1). The signal/reference labels are matched pair by pair, without photon cutoff.
--   - `eprInput`: PDF pp.6,11: actual EPR density, not a covariance placeholder.
--   - `noonAmplitude`: PDF p.12, (74): the n=1 NOON ket (|2,0>+|0,2>)/sqrt(2).
--   - `noonInput`: PDF p.12, (74): normalized two-excitation NOON density; signal mean is ONE.
--   - `fockInput`: PDF p.12, (75): actual number-state projector, natural photon label.
--   - `orthogonalSqueezedVacuum`: PDF p.12: p-squeezed vacuum coefficients. Positive even coefficients mean q is antisqueezed and p squeezed for q=a+a*,p=i(a*-a). Thus real displacement along q is orthogonal to the squeezed axis. xi>=0 is the squeezing magnitude.
--   - `squeezedAmplitude`: PDF p.12: <m|D(alpha)S(xi)|0>, from the actual displacement Fock matrix. For finite real alpha,xi this series converges by the Hilbert inner-product inequality; it is not a covariance-only description.
--   - `squeezedInput`: PDF p.12: unassisted squeezed coherent projector in the full number basis.
--   - `squeezedValue`: PDF p.12/Fig.9: optimization ONLY over the real orthogonally squeezed family, with exact one-photon signal energy alpha^2+sinh(xi)^2=1.
--   - `eprError`: PDF p.5, (15): the optimal binary error for this FIXED transmitter. traceSize is the full nuclear/trace norm; all binary measurements are optimized.
--   - `eprErrorRate`: PDF p.13, (76): the source's error-entropy quantity, not arbitrary measured MI.
--   - `thetaFinite`: PDF p.13, (77): n/s MULTIPLIES (1-sqrt(kappa0)); s>=1 in every result.
--   - `eprLowerRate`: PDF p.13, (78): the scalar guaranteed readable-rate lower bound.
--   - `thetaLimit`: PDF pp.6,13, (33),(79): limiting error bound, not an infinite-copy input state.
--   - `eprLimitRate`: PDF p.13, (79): limiting scalar rate Q_infinity.
--   - `effectProbability`: PDF p.4, (7): Born probability Tr(E rho), with a bounded effect and trace-class rho. The outer trace and inner matrix-vector series converge.
--   - `binaryMeasuredInformation`: PDF p.13: actual mutual information in bits of an equal-prior binary POVM. Unlike (76), it allows an asymmetric induced classical channel.
--   - `SingleCellAchievable`: PDF p.13: existence of a single-cell measurement achieving at least R bits. Such one-cell measurements can be repeated independently across memory cells.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, https://arxiv.org/abs/1107.3500v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

/-!
Quantum Reading Capacity, arXiv:1107.3500v1, PDF pp.3--16.
All registers are completed Hilbert spaces with the full number basis.
Capacities below are the single-cell Holevo optimizations of (46),(51),(65):
identical inputs across different cells and arbitrary collective output detection.
No entanglement across different cells is optimized. Extended relative entropy
makes chi meaningful even when individual output entropies are infinite.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq

/-!
Frozen-name repair: finite-matrix channel powers and effects cannot replace
operations on completed bosonic spaces. TensorCopyBasis allows an arbitrary
basis type, unlike the accepted finite-dimension Register or real-label oracle
Register. finiteMemoryHolevoBits uses extended relative entropy for a fixed
finite memory ensemble, unlike the accepted finite-entropy difference
holevoBits. transmitterInformation applies the stored-channel ensemble to ONE
input, unlike feedback-protocol or finite-channel information.
quantumReadingCapacity and classicalReadingCapacity optimize reading a fixed
channel ensemble at exact signal energy, not transmission of quantum data or
zero-error graph capacities. IsClassicalCellTransmitter and
coherentProductProjector use arbitrary signal/reference mode counts and
coefficient barycenters, whereas Dependency50.P39's same-name objects are
single-mode bounded operators. The frozen coherent coefficients, full-Fock
vacuum dilation, photon expectation and bounded binary effects ARE imported.
No frozen definition is edited, shadowed or silently substituted.
-/

/-- PDF pp.3--4: basis labels for s copies of the COMMON system, including s=0. -/
abbrev TensorCopyBasis (I : Type) (s : ℕ) := Fin s → I

/-- PDF pp.4,8: arbitrary reference Hilbert space, independent of the signal space. -/
abbrev AssistedRegister (I A : Type) (s r : ℕ) := TensorCopyBasis I s × TensorCopyBasis A r

/-- PDF pp.4--5: for optical memories, both signal and reference modes are bosonic. -/
abbrev CellRegister (I : Type) (s r : ℕ) := AssistedRegister I I s r

/-- PDF pp.3,8: a finite nonempty ensemble of pairwise distinct CPTP channels.
Distinctness is on states, so irrelevant extensions off trace class cannot count. -/
structure Memory (I : Type) (k : ℕ) where
  nonempty : 0 < k
  prior : Fin k → ℝ≥0
  mass : ∑ x, prior x = 1
  channel : Fin k → Channel I I
  distinct : ∀ x y, x ≠ y → ∃ rho : State I,
    (channel x).val rho.coefficients ≠ (channel y).val rho.coefficients

/-- PDF pp.3--4,8, (5),(43): tensor power on every block of an entangled input.
The recursive slices are trace class on physical inputs; references are untouched. -/
def traceClassChannelCopies {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ) :
    (s : ℕ) → Matrix (TensorCopyBasis I s) (TensorCopyBasis I s) ℂ →
      Matrix (TensorCopyBasis I s) (TensorCopyBasis I s) ℂ
  | 0, X => X
  | s + 1, X => fun a b =>
      traceClassChannelCopies Phi s
        (fun c d => Phi (fun i j => X (Fin.cons i c) (Fin.cons j d)) (a 0) (b 0))
        (Fin.tail a) (Fin.tail b)

/-- PDF p.8, (43): channel on the signal tensor factors only. -/
def cellOutput {I A : Type} {s r : ℕ} (Phi : Matrix I I ℂ → Matrix I I ℂ)
    (rho : Matrix (AssistedRegister I A s r) (AssistedRegister I A s r) ℂ) :=
  tensorApply (traceClassChannelCopies Phi s) rho

/-- PDF p.8, (44): chi in bits, using its relative-entropy formula.
Zero priors contribute zero even if the corresponding relative entropy is infinite.
For normalized finite ensembles this number is finite and bounded by H(prior). -/
def finiteMemoryHolevoBits {J : Type} {k : ℕ} (p : Fin k → ℝ≥0)
    (out : Fin k → Matrix J J ℂ) : ℝ≥0∞ :=
  (∑ x, (p x : ℝ≥0∞) * extendedRelativeEntropyNats (out x)
    (∑ y, ((p y : ℝ) : ℂ) • out y)) / ENNReal.ofReal (Real.log 2)

/-- PDF p.8: conditional information of the one-cell transmitter. -/
def transmitterInformation {I A : Type} {k s r : ℕ} (M : Memory I k)
    (rho : Matrix (AssistedRegister I A s r) (AssistedRegister I A s r) ℂ) : ℝ≥0∞ :=
  finiteMemoryHolevoBits M.prior (fun x => cellOutput (M.channel x).val rho)

/-- PDF p.9, (48): marginal Shannon entropy, in bits, with 0 log 0=0. -/
def memoryEntropy {I : Type} {k : ℕ} (M : Memory I k) : ℝ :=
  -∑ x, (M.prior x : ℝ) * Real.log (M.prior x : ℝ) / Real.log 2

/-- PDF pp.8--9, (46): unconstrained optimal VALUE, not an assumed maximum. -/
def unconstrainedCapacity {I : Type} {k : ℕ} (M : Memory I k) (A : Type) : ℝ≥0∞ :=
  ⨆ s : {s : ℕ // 1 ≤ s}, ⨆ r : ℕ, ⨆ rho : State (AssistedRegister I A s.val r),
    transmitterInformation M rho.coefficients

/-- PDF p.9, (47): pure, unassisted fixed-s optimal value. -/
def pureUnassistedValue {I : Type} {k : ℕ} (M : Memory I k) (s : ℕ) : ℝ≥0∞ :=
  ⨆ psi : PureState (CellRegister I s 0), transmitterInformation M psi.val.coefficients

/-- PDF pp.9,14: pure-input optimal value on fixed signal/reference registers. -/
def pureRegisterValue {I : Type} {k : ℕ} (M : Memory I k) (A : Type) (s r : ℕ) : ℝ≥0∞ :=
  ⨆ psi : PureState (AssistedRegister I A s r), transmitterInformation M psi.val.coefficients

/-- PDF p.4: exact extended mean photon number of the SUM of signal modes.
The extended sum records infinite energy instead of silently returning zero. -/
def signalEnergy {s r : ℕ}
    (rho : Matrix (CellRegister ℕ s r) (CellRegister ℕ s r) ℂ) : ℝ≥0∞ :=
  ∑' a : CellRegister ℕ s r,
    ENNReal.ofReal ((∑ i, a.1 i : ℕ) : ℝ) * ENNReal.ofReal (rho a a).re

/-- PDF pp.13--14, endnote [31]: frozen total photon expectation, with
signal modes first and reference modes last in the combined full-Fock register. -/
def cellTotalPhotonEnergy {s r : ℕ}
    (rho : Matrix (CellRegister ℕ s r) (CellRegister ℕ s r) ℂ) : ℝ≥0∞ :=
  QAlgorithms.Papers.Independent.Support50.P06.totalEnergy (n := s + r)
    (fun a b => rho
      ((fun i => a (Fin.castAdd r i)), (fun j => a (Fin.natAdd s j)))
      ((fun i => b (Fin.castAdd r i)), (fun j => b (Fin.natAdd s j))))

/-- PDF p.9: an energy-INDEPENDENT class of normalized pure inputs on each register. -/
abbrev PureClass := (s r : ℕ) → Set (PureState (CellRegister ℕ s r))

/-- PDF p.9, (52), interpreted by (56): arbitrary Borel probability mixtures
on the SAME registers; component energies need not equal the barycenter energy. -/
def MixtureOf (P : PureClass) {s r : ℕ} (rho : State (CellRegister ℕ s r)) : Prop :=
  ∃ mu : ProbabilityMeasure (PureState (CellRegister ℕ s r)),
    (∀ᵐ psi ∂(mu : Measure (PureState (CellRegister ℕ s r))), psi ∈ P s r) ∧
    IsBarycenter (mu : Measure (PureState (CellRegister ℕ s r)))
      (fun psi => psi.val.coefficients) rho.coefficients

/-- PDF p.9, (54): exact-energy pure-class optimum; the supremum is extended. -/
def pureClassCapacity {k : ℕ} (M : Memory ℕ k) (P : PureClass) (n : ℝ) : ℝ≥0∞ :=
  ⨆ s : {s : ℕ // 1 ≤ s}, ⨆ r : ℕ,
    ⨆ psi : {psi : PureState (CellRegister ℕ s.val r) //
      psi ∈ P s.val r ∧ signalEnergy psi.val.coefficients = ENNReal.ofReal n},
      transmitterInformation M psi.val.val.coefficients

/-- PDF p.9, (53): exact AVERAGE energy in the arbitrary-mixture class. -/
def mixtureClassCapacity {k : ℕ} (M : Memory ℕ k) (P : PureClass) (n : ℝ) : ℝ≥0∞ :=
  ⨆ s : {s : ℕ // 1 ≤ s}, ⨆ r : ℕ,
    ⨆ rho : {rho : State (CellRegister ℕ s.val r) //
      MixtureOf P rho ∧ signalEnergy rho.coefficients = ENNReal.ofReal n},
      transmitterInformation M rho.val.coefficients

/-- PDF p.9: implicit feasibility of pure-class optimization on its energy domain. -/
def EnergyFeasible (P : PureClass) : Prop :=
  ∀ n : ℝ, 0 ≤ n → ∃ (s r : ℕ) (psi : PureState (CellRegister ℕ s r)),
    1 ≤ s ∧ psi ∈ P s r ∧ signalEnergy psi.val.coefficients = ENNReal.ofReal n

/-- PDF pp.5,10: binary pure-loss memory; the arbitrary prior includes endpoints. -/
structure LossMemory where
  kappa0 : ℝ
  kappa1 : ℝ
  kappa0_mem : kappa0 ∈ Set.Icc (0 : ℝ) 1
  kappa1_mem : kappa1 ∈ Set.Icc (0 : ℝ) 1
  distinct : kappa0 ≠ kappa1
  p : ℝ
  p_mem : p ∈ Set.Icc (0 : ℝ) 1

/-- PDF p.5, (13): the frozen full-Fock vacuum attenuator, reindexed from
one-mode words to natural photon labels. The environment bypasses readout. -/
def vacuumLossAction (kappa : ℝ) (rho : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  fun a b => QAlgorithms.Papers.Independent.Next46.P32.pureLoss 1 kappa
    (fun c d => rho (c 0) (d 0)) (fun _ => a) (fun _ => b)

/-- PDF pp.5,10: fixed binary priors, independent of every transmitter optimization. -/
def lossPrior (p : ℝ) (x : Fin 2) : ℝ≥0 :=
  if x = 0 then Real.toNNReal p else Real.toNNReal (1 - p)

/-- PDF pp.8,10: conditional Holevo information for the actual loss-channel outputs. -/
def lossInformation {s r : ℕ} (kappa0 kappa1 p : ℝ)
    (rho : Matrix (CellRegister ℕ s r) (CellRegister ℕ s r) ℂ) : ℝ≥0∞ :=
  finiteMemoryHolevoBits (lossPrior p) (fun x =>
    cellOutput (vacuumLossAction (if x = 0 then kappa0 else kappa1)) rho)

/-- PDF pp.5,10: all coherent product kets, in the full number basis. -/
def coherentAmplitude {s r : ℕ} (alpha : Fin s → ℂ) (beta : Fin r → ℂ)
    (a : CellRegister ℕ s r) : ℂ :=
  (∏ i, coherentCoefficient (alpha i) (a.1 i)) *
    ∏ j, coherentCoefficient (beta j) (a.2 j)

/-- PDF p.10, (68): coherent projector from its actual ket coefficients. -/
def coherentProductProjector {s r : ℕ} (alpha : Fin s → ℂ) (beta : Fin r → ℂ) :
    Matrix (CellRegister ℕ s r) (CellRegister ℕ s r) ℂ :=
  fun a b => coherentAmplitude alpha beta a * star (coherentAmplitude alpha beta b)

/-- PDF pp.5--6, (19)--(22): ALL probability mixtures of coherent products.
The measure may be singular, atomic or continuous; no positive density is required.
Every coefficient is integrable, preventing a default-zero barycenter integral. -/
def IsClassicalCellTransmitter {s r : ℕ}
    (rho : Matrix (CellRegister ℕ s r) (CellRegister ℕ s r) ℂ) : Prop :=
  ∃ mu : ProbabilityMeasure ((Fin s → ℂ) × (Fin r → ℂ)),
    IsBarycenter (mu : Measure ((Fin s → ℂ) × (Fin r → ℂ)))
      (fun z => coherentProductProjector z.1 z.2) rho

/-- PDF p.9, (51): quantum capacity at exact TOTAL signal energy n per cell. -/
def quantumReadingCapacity (M : LossMemory) (n : ℝ) : ℝ≥0∞ :=
  ⨆ s : {s : ℕ // 1 ≤ s}, ⨆ r : ℕ,
    ⨆ rho : {rho : State (CellRegister ℕ s.val r) //
      signalEnergy rho.coefficients = ENNReal.ofReal n},
      lossInformation M.kappa0 M.kappa1 M.p rho.val.coefficients

/-- PDF p.10, (65): independently defined classical optimization, not H(xi). -/
def classicalReadingCapacity (M : LossMemory) (n : ℝ) : ℝ≥0∞ :=
  ⨆ s : {s : ℕ // 1 ≤ s}, ⨆ r : ℕ,
    ⨆ rho : {rho : State (CellRegister ℕ s.val r) //
      IsClassicalCellTransmitter rho.coefficients ∧ signalEnergy rho.coefficients = ENNReal.ofReal n},
      lossInformation M.kappa0 M.kappa1 M.p rho.val.coefficients

/-- PDF pp.13--14: independently optimized capacity under the stronger constraint. -/
def classicalTotalCapacity (M : LossMemory) (n : ℝ) : ℝ≥0∞ :=
  ⨆ s : {s : ℕ // 1 ≤ s}, ⨆ r : ℕ,
    ⨆ rho : {rho : State (CellRegister ℕ s.val r) //
      IsClassicalCellTransmitter rho.coefficients ∧ cellTotalPhotonEnergy rho.coefficients = ENNReal.ofReal n},
      lossInformation M.kappa0 M.kappa1 M.p rho.val.coefficients

/-- PDF p.10, (67): the larger eigenvalue, including arbitrary endpoint priors. -/
def classicalEigenvalue (M : LossMemory) (n : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - 4 * M.p * (1 - M.p) *
    (1 - Real.exp (-n * (Real.sqrt M.kappa1 - Real.sqrt M.kappa0) ^ 2)))) / 2

/-- PDF p.10, (66): the scalar expression asserted EQUAL to the optimized capacity. -/
def classicalFormula (M : LossMemory) (n : ℝ) : ℝ :=
  binaryEntropyBits (classicalEigenvalue M n)

/-- PDF p.10, (72): one signal, no reference, amplitude sqrt(n). -/
def coherentInput (n : ℝ) : Matrix (CellRegister ℕ 1 0) (CellRegister ℕ 1 0) ℂ :=
  coherentProductProjector (fun _ => (Real.sqrt n : ℂ)) (fun i => Fin.elim0 i)

/-- PDF pp.6,11, (24)--(25): source-defined classical error-entropy rate.
This expression is not the mutual information of every binary measurement. -/
def classicalSingleRate (M : LossMemory) (n : ℝ) : ℝ :=
  1 - binaryEntropyBits ((1 - Real.sqrt (1 -
    Real.exp (-n * (Real.sqrt M.kappa0 - Real.sqrt M.kappa1) ^ 2))) / 2)

/-- PDF pp.6,11--13, (26)--(28): s TMSV pairs, total SIGNAL energy n.
Each pair has Schmidt probabilities (n/s)^m/(1+n/s)^(m+1).
The signal/reference labels are matched pair by pair, without photon cutoff. -/
def eprAmplitude (s : ℕ) (n : ℝ) (a : CellRegister ℕ s s) : ℂ :=
  if a.1 = a.2 then
    (∏ i, Real.sqrt ((n / s) ^ a.1 i / (1 + n / s) ^ (a.1 i + 1)) : ℝ)
  else 0

/-- PDF pp.6,11: actual EPR density, not a covariance placeholder. -/
def eprInput (s : ℕ) (n : ℝ) : Matrix (CellRegister ℕ s s) (CellRegister ℕ s s) ℂ :=
  fun a b => eprAmplitude s n a * star (eprAmplitude s n b)

/-- PDF p.12, (74): the n=1 NOON ket (|2,0>+|0,2>)/sqrt(2). -/
def noonAmplitude (a : CellRegister ℕ 1 1) : ℂ :=
  if (a.1 0 = 2 ∧ a.2 0 = 0) ∨ (a.1 0 = 0 ∧ a.2 0 = 2)
    then (1 / Real.sqrt 2 : ℝ) else 0

/-- PDF p.12, (74): normalized two-excitation NOON density; signal mean is ONE. -/
def noonInput : Matrix (CellRegister ℕ 1 1) (CellRegister ℕ 1 1) ℂ :=
  fun a b => noonAmplitude a * star (noonAmplitude b)

/-- PDF p.12, (75): actual number-state projector, natural photon label. -/
def fockInput (m : ℕ) : Matrix (CellRegister ℕ 1 0) (CellRegister ℕ 1 0) ℂ :=
  fun a b => if a.1 0 = m ∧ b.1 0 = m then 1 else 0

/-- PDF p.12: p-squeezed vacuum coefficients. Positive even coefficients mean
q is antisqueezed and p squeezed for q=a+a*,p=i(a*-a). Thus real displacement
along q is orthogonal to the squeezed axis. xi>=0 is the squeezing magnitude. -/
def orthogonalSqueezedVacuum (xi : ℝ) (m : ℕ) : ℝ :=
  if m % 2 = 0 then
    Real.sqrt (Nat.factorial m : ℝ) * Real.tanh xi ^ (m / 2) /
      (Real.sqrt (Real.cosh xi) * 2 ^ (m / 2) * (Nat.factorial (m / 2) : ℝ))
  else 0

/-- PDF p.12: <m|D(alpha)S(xi)|0>, from the actual displacement Fock matrix.
For finite real alpha,xi this series converges by the Hilbert inner-product
inequality; it is not a covariance-only description. -/
def squeezedAmplitude (alpha xi : ℝ) (m : ℕ) : ℂ :=
  ∑' j : ℕ, displacementMatrix (alpha : ℂ) m j * (orthogonalSqueezedVacuum xi j : ℂ)

/-- PDF p.12: unassisted squeezed coherent projector in the full number basis. -/
def squeezedInput (alpha xi : ℝ) :
    Matrix (CellRegister ℕ 1 0) (CellRegister ℕ 1 0) ℂ :=
  fun a b => squeezedAmplitude alpha xi (a.1 0) * star (squeezedAmplitude alpha xi (b.1 0))

/-- PDF p.12/Fig.9: optimization ONLY over the real orthogonally squeezed family,
with exact one-photon signal energy alpha^2+sinh(xi)^2=1. -/
def squeezedValue (kappa1 : ℝ) : ℝ≥0∞ :=
  ⨆ z : {z : ℝ × ℝ // 0 ≤ z.2 ∧ z.1 ^ 2 + Real.sinh z.2 ^ 2 = 1},
    lossInformation 0 kappa1 (1 / 2) (squeezedInput z.val.1 z.val.2)

/-- PDF p.5, (15): the optimal binary error for this FIXED transmitter.
traceSize is the full nuclear/trace norm; all binary measurements are optimized. -/
def eprError (kappa0 : ℝ) (s : ℕ) (n : ℝ) : ℝ :=
  (1 - (traceSize (cellOutput (vacuumLossAction kappa0) (eprInput s n) -
    cellOutput (vacuumLossAction 1) (eprInput s n))).toReal / 2) / 2

/-- PDF p.13, (76): the source's error-entropy quantity, not arbitrary measured MI. -/
def eprErrorRate (kappa0 : ℝ) (s : ℕ) (n : ℝ) : ℝ :=
  1 - binaryEntropyBits (eprError kappa0 s n)

/-- PDF p.13, (77): n/s MULTIPLIES (1-sqrt(kappa0)); s>=1 in every result. -/
def thetaFinite (kappa0 : ℝ) (s : ℕ) (n : ℝ) : ℝ :=
  1 / (2 * (1 + (n / s) * (1 - Real.sqrt kappa0)) ^ (2 * s))

/-- PDF p.13, (78): the scalar guaranteed readable-rate lower bound. -/
def eprLowerRate (kappa0 : ℝ) (s : ℕ) (n : ℝ) : ℝ :=
  1 - binaryEntropyBits (thetaFinite kappa0 s n)

/-- PDF pp.6,13, (33),(79): limiting error bound, not an infinite-copy input state. -/
def thetaLimit (kappa0 n : ℝ) : ℝ :=
  Real.exp (-2 * n * (1 - Real.sqrt kappa0)) / 2

/-- PDF p.13, (79): limiting scalar rate Q_infinity. -/
def eprLimitRate (kappa0 n : ℝ) : ℝ :=
  1 - binaryEntropyBits (thetaLimit kappa0 n)

/-- PDF p.4, (7): Born probability Tr(E rho), with a bounded effect and
trace-class rho. The outer trace and inner matrix-vector series converge. -/
def effectProbability {J : Type} (E : Hilbert J →L[ℂ] Hilbert J)
    (rho : Matrix J J ℂ) : ℝ :=
  (∑' i : J, ∑' j : J, (E (lp.single 2 j 1)) i * rho j i).re

/-- PDF p.13: actual mutual information in bits of an equal-prior binary POVM.
Unlike (76), it allows an asymmetric induced classical channel. -/
def binaryMeasuredInformation {J : Type} (E : Hilbert J →L[ℂ] Hilbert J)
    (out0 out1 : Matrix J J ℂ) : ℝ :=
  let joint : Fin 2 → Fin 2 → ℝ := fun x z =>
    let t := effectProbability E (if x = 0 then out0 else out1)
    (if z = 0 then t else 1 - t) / 2
  ∑ x, ∑ z, if joint x z = 0 then 0 else
    joint x z * Real.log (joint x z / ((∑ y, joint y z) / 2)) / Real.log 2

/-- PDF p.13: existence of a single-cell measurement achieving at least R bits.
Such one-cell measurements can be repeated independently across memory cells. -/
def SingleCellAchievable (kappa0 : ℝ) (s : ℕ) (n R : ℝ) : Prop :=
  ∃ E : Hilbert (CellRegister ℕ s s) →L[ℂ] Hilbert (CellRegister ℕ s s),
    IsBinaryEffect E ∧ R ≤ binaryMeasuredInformation E
      (cellOutput (vacuumLossAction kappa0) (eprInput s n))
      (cellOutput (vacuumLossAction 1) (eprInput s n))

/-! Sanity checks pin conventions; no source theorem is proved here. -/

example {I : Type} (Phi : Matrix I I ℂ → Matrix I I ℂ)
    (X : Matrix (TensorCopyBasis I 0) (TensorCopyBasis I 0) ℂ) : traceClassChannelCopies Phi 0 X = X := rfl

example {I : Type} {k : ℕ} (M : Memory I k) : 0 < k := M.nonempty

example {I : Type} {s r : ℕ} (psi : PureState (CellRegister I s r)) :
    ∃ u : Hilbert (CellRegister I s r), ‖u‖ = 1 ∧
      psi.val.coefficients = QAlgorithms.Papers.Independent.Dependency50.P33.rankOne u := psi.property

example : binaryEntropyBits 0 = 0 := by simp [binaryEntropyBits]

example : binaryEntropyBits 1 = 0 := by simp [binaryEntropyBits]

example (kappa : ℝ) (s : ℕ) : thetaFinite kappa s 0 = 1 / 2 := by
  simp [thetaFinite]

example (kappa : ℝ) : thetaLimit kappa 0 = 1 / 2 := by simp [thetaLimit]

example (kappa n : ℝ) : thetaFinite kappa 1 n =
    1 / (2 * (1 + n * (1 - Real.sqrt kappa)) ^ 2) := by simp [thetaFinite]

example (m : ℕ) (a b : CellRegister ℕ 1 0) :
    fockInput m a b = if a.1 0 = m ∧ b.1 0 = m then 1 else 0 := rfl

example (a : CellRegister ℕ 1 1) :
    noonAmplitude a = if (a.1 0 = 2 ∧ a.2 0 = 0) ∨ (a.1 0 = 0 ∧ a.2 0 = 2)
      then ((1 / Real.sqrt 2 : ℝ) : ℂ) else (0 : ℂ) := rfl

example : orthogonalSqueezedVacuum 0 0 = 1 := by
  simp [orthogonalSqueezedVacuum]

example (xi : ℝ) : orthogonalSqueezedVacuum xi 1 = 0 := by
  simp [orthogonalSqueezedVacuum]

end QAlgorithms.Papers.Independent.Advance50.P35


