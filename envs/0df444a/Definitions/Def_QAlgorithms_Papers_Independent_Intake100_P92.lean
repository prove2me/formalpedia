-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92
-- name    : QAlgorithms_Papers_Independent_Intake100_P92
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:29:04.462914+00:00
-- url     : https://prove2.me/theorems/390cb1d9-b868-458e-bdfc-713aaffb9dec
-- title:
--   Definitions for Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift)
-- statement:
--   The objects the formalized statements of *Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift)* (arXiv:0710.4884) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `splitter`: PDF p.3: the channel beam splitter; detector loss is not given to Eve.
--   - `clickWeight`: PDF pp.2–3: threshold detection with trusted efficiency and no dark counts.
--   - `eventWeight`: PDF p.2: exactly one selected detector clicks in a two-mode time bin.
--   - `thresholdEventProbability`: PDF pp.2–3: Born probability for the specified threshold-detector event, on full Fock space. Reuse assessment: Unlike the accepted finite classical CQ event sum in Gap48.P11, this is an infinite photon-occupation Born sum with trusted detector efficiency.
--   - `visibility`: PDF p.2: the observed interferometric visibility; used conditionally only when the sum of the port probabilities is positive.
--   - `ancillaGram`: PDF p.3, (1): Gram matrix of a finite list of already weighted vectors. Its nonzero spectrum is that of the sum of their rank-one operators, also when the vectors lie in the infinite- dimensional Fock Hilbert space. Reuse assessment: Unlike Claimed50.P48.gram, this uses the source order <x_i|x_j> and supports arbitrary Hilbert vectors, including full Fock space; MitigationTomography.gram is a real calibration matrix.
--   - `ensembleEntropyBits`: PDF p.3, (1): spectral von Neumann entropy, in bits, of a finite ensemble. The real function has the continuous zero-eigenvalue value 0 log 0 = 0. Reuse assessment: The indexed entropy declarations take operators or classical laws (several in nats), not weighted vectors in an arbitrary Hilbert space. This interface constructs its finite Gram operator in bits.
--   - `equiprobableEnsemble`: Equal mixture, retaining its full ensemble rather than substituting an overlap. Reuse assessment: The indexed average declarations mix matrices or structured ensembles; here a tagged list of Hilbert vectors is scaled by sqrt(1/2).
--   - `binaryHolevoBits`: PDF p.3, (1): binary, equiprobable Holevo information of actual ensembles. Reuse assessment: The indexed chi declarations are a degree-six matrix invariant (Information100.P60) or a reference-output state (Information100.P76), not binary ensemble Holevo information.
--   - `weightedAncillaTrace`: Trace of the positive ensemble operator, including subnormalized ensembles. Reuse assessment: Information100.P19.mass takes a finite bipartite operator, not an ensemble of arbitrary Hilbert vectors.
--   - `ensembleDensityCoefficients`: Actual density-operator coefficients, with no photon-number cutoff. Reuse assessment: Dependency50.P19.Spectrum.density constructs an operator from a finite normalized spectral decomposition; this sum constructs coordinate coefficients from weighted vectors, allowing infinite output indices.
--   - `HasUnitaryGramSpectrum`: Spectral assertion includes multiplicities and zero eigenvalues of the Gram matrix. Reuse assessment: Gap20.P17.HasSpectrum is a characteristic-polynomial predicate with a Fin k eigenvalue list; this predicate records an actual unitary diagonalization with the same arbitrary finite index type.
--   - `dw`: PDF p.3, (2): signed ideal direct/reverse reconciliation expression. A nonnegative operational yield may abort at zero; it is not defined here.
--   - `dpsPhaseSign`: PDF pp.2–3: true is phase minus, false is phase plus. Reuse assessment: Renew46.P14.sign is real-valued and uses true for plus; this complex-valued DPS convention uses true for minus.
--   - `eveAmplitude`: PDF p.3, (3): Eve's retained amplitude, using channel loss only.
--   - `gammaE`: PDF p.3, (3): gamma_E; mu is computed from alpha rather than assumed separately.
--   - `click`: PDF p.2: exact coherent pulse click probability.
--   - `cowE`: PDF p.3, (4): actual pure COW conditional state, including its vacuum factor.
--   - `dpsE`: PDF p.3, (6): actual DPS conditional mixture over its unknown absolute phase.
--   - `cowBob`: PDF p.2: COW Bob state before detection.
--   - `dpsBob`: PDF pp.2–3: the two output modes at one DPS interference time. Each neighbor contributes half its amplitude after the delay interferometer; other times are traced out. This accounts for the source's per-time-slot prefactor.
--   - `herald`: Full diagonal-event partial trace on a Bob–Eve product coefficient array. This definition computes the postselected operator rather than assuming it.
--   - `cowHerald`: PDF p.3: COW detected-bit conditional operator, before dividing by its trace.
--   - `dpsHerald`: PDF p.3: DPS detected-bit operator, averaging the equiprobable absolute signs.
--   - `cowRate`: PDF pp.3–4, (5),(7): BSA signed rate, calculated from constructed Eve ensembles. The same COW function applies to both modifications with Alice's pairings.
--   - `dpsRate`: PDF p.4, (7): DPS BSA rate from its two mixed conditional operators.
--   - `PulsePair`: Occupancy pair: true is a nonempty pulse. Photon-slot false means 10.
--   - `PairData`: PDF pp.5–8: vacuum and photon ancilla data for one repeated disjoint-pair attack.
--   - `pairDistance`: Number of differing pulse occupancies/signs.
--   - `pulseWeight`: PDF p.5: imperfect-modulator photon weight for an empty/occupied input slot.
--   - `cowOutput`: PDF pp.5–6, (9),(17): the three retained Bob sectors, with the source's uncorrected vacuum coefficient. This is a leading-order coefficient array only.
--   - `CowValid`: PDF pp.5–6, (10)–(14),(18): normalized leading-order COW Gram constraints. The Boolean flag enables the additional vacuum-input constraints for COWm1. Every separately monitored nonempty boundary is checked, not an average visibility.
--   - `keyPair`: Source key bit: 0 is mu,0 and 1 is 0,mu.
--   - `errorSlot`: PDF pp.5–6: the four unconstrained error flags, including vacuum input.
--   - `errorIndex`: Distinct labels for those four error vectors.
--   - `liftVec`: Coordinate isometric embedding used to add independent orthogonal flags.
--   - `flaggedPair`: PDF pp.5–6: maximizing orthogonal error flags are constructed in extra coordinates. They are not a hypothesis imposed on every attack.
--   - `cowA`: PDF p.5: Eve's actual Alice-conditioned COW ensemble.
--   - `cowB`: PDF p.5: Eve's Bob-conditioned ensemble, summing over Alice's bit.
--   - `cowLeak`: PDF p.6, (15): source expression evaluated on the actual correct-state overlap.
--   - `cowCoefficient`: PDF p.6, (16): first-order COW coefficient, computed from flagged ensembles.
--   - `crossCow`: PDF pp.6–7, (19)–(25): crossing-pair conditional ensemble. The source relation j_prime = 1-k = a is built into both copies; the outer bits j,k_prime are averaged.
--   - `crossCowB`: PDF p.7, (23): the Bob marginal sums over a, with b held fixed.
--   - `crossCorrect`: PDF p.7, (24),(25): correct crossing states rho_4^(a,a).
--   - `cowm1Info`: PDF p.7, (42 analogue): the public alignment flag is retained by Eve.
--   - `cowm1Leak`: PDF p.7, (26): same-pair pure-state information plus crossing-pair Holevo.
--   - `OneData`: PDF p.7, (28): a repeated one-pulse ancilla assignment.
--   - `CowOneValid`: PDF p.7, (29),(30): all one-pulse COWm2 Gram constraints.
--   - `flaggedOne`: PDF p.7: construct the free p_0 as an orthogonal error flag.
--   - `oneToPair`: PDF p.8, (31): product vectors for the two key pulses, from the same 1PA.
--   - `DpsValid`: PDF p.8, (34)–(39): all DPS 2PA vacuum/photon norms and monitored Gram data. Here pulse-pair Booleans label signs, not occupancies.
--   - `dpsOutput`: PDF p.8, (34): normalized-ancilla, first-order Bob-sector array only.
--   - `dps2Psi`: PDF p.9, Case 1: unnormalized interferometer ancilla vector.
--   - `dps4Psi`: PDF p.9, Case 2: crossing interference uses slots two and three.
--   - `dps2Joint`: PDF p.9: joint conditional block for Alice a, Bob b, same attacked pair.
--   - `dps2A`: PDF p.9: same-pair Alice marginal, retaining the factor 1/8.
--   - `dps2B`: PDF p.9: same-pair Bob marginal.
--   - `dps4Joint`: PDF p.9: crossing-pair joint block with the factor 1/32.
--   - `dps4A`: PDF p.9: crossing Alice marginal; bit a is the relative sign of slots 2,3.
--   - `dps4B`: PDF p.9: crossing Bob marginal.
--   - `dpsInfo`: PDF p.9, (42): Eve keeps the public same-pair/crossing-pair alignment flag.
--   - `bobPairLaw`: PDF pp.9,12: balanced independent companion choice after a click. This is exactly the source's one-half acceptance model, not an arbitrary schedule.
--   - `zLaw`: Appendix A p.11: actual Z-channel joint law, q = nonempty fraction, x = click probability conditional on a nonempty pulse.
--   - `zInfo`: Appendix A p.11: ideal mutual information from the actual channel law.
--   - `zCoefficient`: Appendix A p.11: coefficient of the small-click-probability information.
--   - `idealSiftingCoefficient`: Appendix A pp.11–12: original COW, COWm1, COWm2, random consecutive pairing, and Bob pairing, in that order. Nonempty fraction is one half; the last two choices accept only mixed pairs.
--   - `idealBitLaw`: Ideal sifted uniform bits are perfectly correlated; no security is asserted.
--   - `announcedLaw`: Appendix A p.11: joint on/off law restricted to announced slots. Every click is kept, and the same fraction of no-click slots is selected independently of Alice's input. f0 is the unconditional selected no-click fraction.
--   - `rvec`: Real coordinate vector, used only for the paper's explicit appendix families.
--   - `basis`: Coordinate basis vector; added flag dimensions are kept separate.
--   - `cowMinimum`: Appendix B p.13, (B8): positive-regime correct-state overlap.
--   - `cowPositive`: Appendix B pp.12–13, (B4),(B5),(B8),(B9): explicit minimizing key vectors and decoy completion. Error vectors will be added by flaggedPair.
--   - `cowZero`: Appendix B p.13: a feasible zero-overlap construction, including V=0 and V=1/2. The printed illustrative angle quotient is not used. The low-V branch uses extra orthogonal residuals. The high-V branch solves the overlap equation for its actual cosine; its denominator is positive in that branch. Decoy photon residuals are independent of the key-vector residuals.
--   - `cowm1Family`: Appendix C p.14, (C2)–(C10): the displayed four-dimensional participating vectors. The four unconstrained error states live in separately added dimensions. The printed parenthetical identifying decoy photon vectors as orthogonal error flags is corrected to the vacuum-input vectors specified in Section IV B.
--   - `cowm2Minimum`: Appendix D pp.14–15: minimum single-pulse overlap, including the zero regime.
--   - `cowm2Optimum`: Appendix D p.15, (D3),(D4): piecewise witness without singular endpoint angle quotients. p_0 is a fourth, independent coordinate outside the three participating vectors. The V=0 branch is treated before the cosine quotient.
--   - `DpsOneValid`: Appendix E p.16, (E1)–(E3): normalized leading-order DPS one-pulse data. All sign-conditioned visibilities are checked separately.
--   - `dps1Psi`: Appendix E p.16: actual product ancilla after the DPS interferometer.
--   - `dps1Joint`: Appendix E p.16: subnormalized block rho^(a,b), with the source's factor 1/8.
--   - `dps1A`: Appendix E p.16: Alice marginal, summing Bob's outcome.
--   - `dps1B`: Appendix E p.16: Bob marginal, correctly summing Alice's bit a. Printed: a sum over b while b remains free. Changed: sum over a, as required by conditional marginalization and the matching construction on p.9.
--   - `dpsOneFamily`: Appendix E pp.16–17, (E5)–(E8): the complete six-parameter family. The half-angle phases and the relative minus sign in w_minus are retained.
--   - `oneFamilyVectors`: All four one-pulse vectors, with a common photon phase gauge.
--   - `SameSpanGeometry`: Equality of finite vector geometry, explicitly witnessed by an isometry of their spans. This preserves every constructed conditional operator spectrum.
--   - `dpsRestrictedVacuum`: Appendix E p.17, (E11): exact symmetric vacuum vectors, embedded in six real coordinates. The third/fourth coordinates are sqrt((1-gamma^2)/2).
--   - `dpsRestricted`: Appendix E p.17, (E13),(E14): actual photon vectors are constructed from unit auxiliary data; their normalization and visibility are conclusions below.
--   - `cowIdealLeak`: Section IV E p.9: the long-distance COW BSA information.
--   - `dpsIdealLeak`: Section IV E p.9 and Appendix E pp.17–18: long-distance DPS BSA information.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, https://arxiv.org/abs/0710.4884v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

/-!
Branciard–Gisin–Scarani, arXiv:0710.4884v2. Exact BSA results use full Fock
states. Noisy attacks below are normalized ancilla Gram models at leading
order only; they are not asserted to be finite-loss isometries. Rates are signed
Devetak–Winter expressions per emitted time slot, with ideal error correction,
balanced key bits, trusted detectors, no dark counts/dead times, negligible
unused/decoy fraction, and the apparatus prefactors omitted by the paper.
The finite-ensemble Gram entropy is the von Neumann entropy of the actual
finite-rank ensemble operator; it uses every vector and its weight.
-/

noncomputable section

open scoped Matrix ComplexConjugate
open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)
open QAlgorithms.Papers.Independent.Information100.P75 (phase)

namespace Optics

open QAlgorithms.Papers.Independent.Frontier18.P14

/-- PDF p.3: the channel beam splitter; detector loss is not given to Eve. -/
def splitter (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt t : ℂ), -(Real.sqrt (1-t) : ℂ);
     (Real.sqrt (1-t) : ℂ), (Real.sqrt t : ℂ)]

/-- PDF pp.2–3: threshold detection with trusted efficiency and no dark counts. -/
def clickWeight (eta : ℝ) (n : ℕ) : ℝ := 1 - (1-eta)^n

/-- PDF p.2: exactly one selected detector clicks in a two-mode time bin. -/
def eventWeight (eta : ℝ) (b : Bool) (n : ℕ × ℕ) : ℝ :=
  if b then (1-eta)^n.1 * clickWeight eta n.2
  else clickWeight eta n.1 * (1-eta)^n.2

/-- PDF pp.2–3: Born probability for the specified threshold-detector event, on full Fock space.

Reuse assessment: Unlike the accepted finite classical CQ event sum in Gap48.P11, this is an
infinite photon-occupation Born sum with trusted detector efficiency.
-/
def thresholdEventProbability (eta : ℝ) (b : Bool) (psi : Fock) : ℝ :=
  ∑' n : ℕ × ℕ, eventWeight eta b n * Complex.normSq (psi n)

/-- PDF p.2: the observed interferometric visibility; used conditionally only
when the sum of the port probabilities is positive. -/
def visibility (eta : ℝ) (psi : Fock) : ℝ :=
  (thresholdEventProbability eta false psi - thresholdEventProbability eta true psi) /
    (thresholdEventProbability eta false psi + thresholdEventProbability eta true psi)

example (eta : ℝ) : clickWeight eta 0 = 0 := by simp [clickWeight]

end Optics

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- PDF p.3, (1): Gram matrix of a finite list of already weighted vectors. Its nonzero spectrum is
that of the sum of their rank-one operators, also when the vectors lie in the infinite-
dimensional Fock Hilbert space.

Reuse assessment: Unlike Claimed50.P48.gram, this uses the source order <x_i|x_j> and supports
arbitrary Hilbert vectors, including full Fock space; MitigationTomography.gram is a real
calibration matrix.
-/
def ancillaGram {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : I → H) : Matrix I I ℂ :=
  fun i j => inner ℂ (x i) (x j)

/-- PDF p.3, (1): spectral von Neumann entropy, in bits, of a finite ensemble. The real function has
the continuous zero-eigenvalue value 0 log 0 = 0.

Reuse assessment: The indexed entropy declarations take operators or classical laws (several in
nats), not weighted vectors in an arbitrary Hilbert space. This interface constructs its finite
Gram operator in bits.
-/
def ensembleEntropyBits {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : I → H) : ℝ :=
  (Matrix.trace (cfc (fun z : ℝ => -z * Real.log z / Real.log 2) (ancillaGram x))).re

/-- Equal mixture, retaining its full ensemble rather than substituting an overlap.

Reuse assessment: The indexed average declarations mix matrices or structured ensembles; here a
tagged list of Hilbert vectors is scaled by sqrt(1/2).
-/
def equiprobableEnsemble {I H : Type*} [SMul ℂ H] (x y : I → H) : Bool × I → H :=
  fun z => (Real.sqrt (1/2) : ℂ) • (if z.1 then y z.2 else x z.2)

/-- PDF p.3, (1): binary, equiprobable Holevo information of actual ensembles.

Reuse assessment: The indexed chi declarations are a degree-six matrix invariant
(Information100.P60) or a reference-output state (Information100.P76), not binary ensemble
Holevo information.
-/
def binaryHolevoBits {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : I → H) : ℝ :=
  ensembleEntropyBits (equiprobableEnsemble x y) - ensembleEntropyBits x / 2 - ensembleEntropyBits y / 2

/-- Trace of the positive ensemble operator, including subnormalized ensembles.

Reuse assessment: Information100.P19.mass takes a finite bipartite operator, not an ensemble of
arbitrary Hilbert vectors.
-/
def weightedAncillaTrace {I H : Type*} [Fintype I] [NormedAddCommGroup H] (x : I → H) : ℝ :=
  ∑ i, ‖x i‖^2

/-- Actual density-operator coefficients, with no photon-number cutoff.

Reuse assessment: Dependency50.P19.Spectrum.density constructs an operator from a finite
normalized spectral decomposition; this sum constructs coordinate coefficients from weighted
vectors, allowing infinite output indices.
-/
def ensembleDensityCoefficients {I J : Type*} [Fintype I] (x : I → J → ℂ) : Matrix J J ℂ :=
  fun j k => ∑ i, x i j * star (x i k)

/-- Spectral assertion includes multiplicities and zero eigenvalues of the Gram matrix.

Reuse assessment: Gap20.P17.HasSpectrum is a characteristic-polynomial predicate with a Fin k
eigenvalue list; this predicate records an actual unitary diagonalization with the same
arbitrary finite index type.
-/
def HasUnitaryGramSpectrum {I : Type*} [Fintype I] [DecidableEq I]
    (G : Matrix I I ℂ) (e : I → ℝ) : Prop :=
  ∃ U : Matrix I I ℂ, U ∈ Matrix.unitaryGroup I ℂ ∧
    G = U * Matrix.diagonal (fun i => (e i : ℂ)) * U.conjTranspose

/-- PDF p.3, (2): signed ideal direct/reverse reconciliation expression.
A nonnegative operational yield may abort at zero; it is not defined here. -/
def dw (sift Q chiA chiB : ℝ) : ℝ :=
  sift * (1 - QAlgorithms.binEntropy2 Q - min chiA chiB)

/-- PDF pp.2–3: true is phase minus, false is phase plus.

Reuse assessment: Renew46.P14.sign is real-valued and uses true for plus; this complex-valued
DPS convention uses true for minus.
-/
def dpsPhaseSign (b : Bool) : ℂ := if b then -1 else 1

/-- PDF p.3, (3): Eve's retained amplitude, using channel loss only. -/
def eveAmplitude (alpha : ℂ) (t : ℝ) : ℂ := (Real.sqrt (1-t) : ℂ) * alpha

/-- PDF p.3, (3): gamma_E; mu is computed from alpha rather than assumed separately. -/
def gammaE (alpha : ℂ) (t : ℝ) : ℝ := Real.exp (-Complex.normSq alpha * (1-t))

/-- PDF p.2: exact coherent pulse click probability. -/
def click (mu t eta : ℝ) : ℝ := 1 - Real.exp (-mu*t*eta)

/-- PDF p.3, (4): actual pure COW conditional state, including its vacuum factor. -/
def cowE (alpha : ℂ) (t : ℝ) (a : Bool) : Unit → Fock :=
  fun _ => if a then coherentPair 0 (eveAmplitude alpha t)
    else coherentPair (eveAmplitude alpha t) 0

/-- PDF p.3, (6): actual DPS conditional mixture over its unknown absolute phase. -/
def dpsE (alpha : ℂ) (t : ℝ) (a : Bool) : Bool → Fock :=
  fun s => (Real.sqrt (1/2) : ℂ) •
    coherentPair (dpsPhaseSign s * eveAmplitude alpha t)
      (dpsPhaseSign (Bool.xor s a) * eveAmplitude alpha t)

/-- PDF p.2: COW Bob state before detection. -/
def cowBob (alpha : ℂ) (t : ℝ) (a : Bool) : Fock :=
  if a then coherentPair 0 ((Real.sqrt t : ℂ)*alpha)
  else coherentPair ((Real.sqrt t : ℂ)*alpha) 0

/-- PDF pp.2–3: the two output modes at one DPS interference time. Each
neighbor contributes half its amplitude after the delay interferometer; other
times are traced out. This accounts for the source's per-time-slot prefactor. -/
def dpsBob (alpha : ℂ) (t : ℝ) (s a : Bool) : Fock :=
  let u := dpsPhaseSign s * (Real.sqrt t : ℂ) * alpha
  let v := dpsPhaseSign (Bool.xor s a) * (Real.sqrt t : ℂ) * alpha
  coherentPair ((u+v)/2) ((u-v)/2)

/-- Full diagonal-event partial trace on a Bob–Eve product coefficient array.
This definition computes the postselected operator rather than assuming it. -/
def herald (eta : ℝ) (b : Bool) (bob eve : Fock) :
    Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun i j => ∑' n : ℕ × ℕ,
    (Optics.eventWeight eta b n : ℂ) * (bob n * eve i) * star (bob n * eve j)

/-- PDF p.3: COW detected-bit conditional operator, before dividing by its trace. -/
def cowHerald (alpha : ℂ) (t eta : ℝ) (a b : Bool) :=
  herald eta b (cowBob alpha t a) (cowE alpha t a ())

/-- PDF p.3: DPS detected-bit operator, averaging the equiprobable absolute signs. -/
def dpsHerald (alpha : ℂ) (t eta : ℝ) (a b : Bool) :
    Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  (1/2 : ℂ) • ∑ s : Bool,
    herald eta b (dpsBob alpha t s a)
      (coherentPair (dpsPhaseSign s * eveAmplitude alpha t)
        (dpsPhaseSign (Bool.xor s a) * eveAmplitude alpha t))

/-- PDF pp.3–4, (5),(7): BSA signed rate, calculated from constructed Eve ensembles.
The same COW function applies to both modifications with Alice's pairings. -/
def cowRate (alpha : ℂ) (t eta : ℝ) : ℝ :=
  dw (click (Complex.normSq alpha) t eta / 2) 0
    (binaryHolevoBits (cowE alpha t false) (cowE alpha t true))
    (binaryHolevoBits (cowE alpha t false) (cowE alpha t true))

/-- PDF p.4, (7): DPS BSA rate from its two mixed conditional operators. -/
def dpsRate (alpha : ℂ) (t eta : ℝ) : ℝ :=
  dw (click (Complex.normSq alpha) t eta) 0
    (binaryHolevoBits (dpsE alpha t false) (dpsE alpha t true))
    (binaryHolevoBits (dpsE alpha t false) (dpsE alpha t true))

example (alpha : ℂ) (t : ℝ) : cowE alpha t false () =
    coherentPair (eveAmplitude alpha t) 0 := rfl

/-- Occupancy pair: true is a nonempty pulse. Photon-slot false means 10. -/
abbrev PulsePair := Bool × Bool

/-- PDF pp.5–8: vacuum and photon ancilla data for one repeated disjoint-pair attack. -/
structure PairData (I : Type*) where
  v : PulsePair → Vec I
  p : PulsePair → Bool → Vec I

/-- Number of differing pulse occupancies/signs. -/
def pairDistance (x y : PulsePair) : ℕ :=
  (if x.1 = y.1 then 0 else 1) + (if x.2 = y.2 then 0 else 1)

/-- PDF p.5: imperfect-modulator photon weight for an empty/occupied input slot. -/
def pulseWeight (Q : ℝ) (occupied : Bool) : ℝ := if occupied then 1-Q else Q

/-- PDF pp.5–6, (9),(17): the three retained Bob sectors, with the source's
uncorrected vacuum coefficient. This is a leading-order coefficient array only. -/
def cowOutput {I : Type*} (A : PairData I) (mu t Q : ℝ) (x : PulsePair) :
    Fin 3 → I → ℂ :=
  fun k i => if k = 0 then A.v x i else if k = 1 then
    (Real.sqrt (pulseWeight Q x.1 * mu*t) : ℂ) * A.p x false i else
    (Real.sqrt (pulseWeight Q x.2 * mu*t) : ℂ) * A.p x true i

/-- PDF pp.5–6, (10)–(14),(18): normalized leading-order COW Gram constraints.
The Boolean flag enables the additional vacuum-input constraints for COWm1.
Every separately monitored nonempty boundary is checked, not an average visibility. -/
def CowValid {I : Type*} [Fintype I] (A : PairData I) (mu V : ℝ)
    (modified : Bool) : Prop :=
  (∀ x, ‖A.v x‖ = 1) ∧ (∀ x b, ‖A.p x b‖ = 1) ∧
  (∀ x y, (modified = true ∨ (x ≠ (false,false) ∧ y ≠ (false,false))) →
    inner ℂ (A.v x) (A.v y) = (Real.exp (-mu*(pairDistance x y : ℝ)/2) : ℂ)) ∧
  (inner ℂ (A.p (true,true) true) (A.p (true,true) false)).re = V ∧
  (∀ (l r : Bool),
    (inner ℂ (A.v (l,true)) (A.p (l,true) true) *
      inner ℂ (A.p (true,r) false) (A.v (true,r))).re = V)

/-- Source key bit: 0 is mu,0 and 1 is 0,mu. -/
def keyPair (a : Bool) : PulsePair := (!a,a)

/-- PDF pp.5–6: the four unconstrained error flags, including vacuum input. -/
def errorSlot (x : PulsePair) (b : Bool) : Bool := !(if b then x.2 else x.1)

/-- Distinct labels for those four error vectors. -/
def errorIndex (x : PulsePair) (b : Bool) : Fin 4 :=
  if x = (false,false) then (if b then 1 else 0) else if x.1 then 2 else 3

/-- Coordinate isometric embedding used to add independent orthogonal flags. -/
def liftVec {I : Type*} (v : Vec I) : Vec (Sum I (Fin 4)) :=
  WithLp.toLp 2 (Sum.elim (fun i => v i) (fun _ => 0))

/-- PDF pp.5–6: maximizing orthogonal error flags are constructed in extra
coordinates. They are not a hypothesis imposed on every attack. -/
def flaggedPair {I : Type*} (A : PairData I) : PairData (Sum I (Fin 4)) where
  v := fun x => liftVec (A.v x)
  p := fun x b => if errorSlot x b then
    WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun j => if j = errorIndex x b then 1 else 0))
    else liftVec (A.p x b)

/-- PDF p.5: Eve's actual Alice-conditioned COW ensemble. -/
def cowA {I : Type*} (A : PairData I) (Q : ℝ) (a : Bool) : Bool → Vec I :=
  fun b => (Real.sqrt (if a = b then 1-Q else Q) : ℂ) • A.p (keyPair a) b

/-- PDF p.5: Eve's Bob-conditioned ensemble, summing over Alice's bit. -/
def cowB {I : Type*} (A : PairData I) (Q : ℝ) (b : Bool) : Bool → Vec I :=
  fun a => (Real.sqrt (if a = b then 1-Q else Q) : ℂ) • A.p (keyPair a) b

/-- PDF p.6, (15): source expression evaluated on the actual correct-state overlap. -/
def cowLeak {I : Type*} [Fintype I] (A : PairData I) (Q : ℝ) : ℝ :=
  Q + (1-Q)*QAlgorithms.binEntropy2
    ((1+‖inner ℂ (A.p (true,false) false) (A.p (false,true) true)‖)/2)

/-- PDF p.6, (16): first-order COW coefficient, computed from flagged ensembles. -/
def cowCoefficient {I : Type*} [Fintype I] [DecidableEq I]
    (A : PairData I) (mu Q : ℝ) : ℝ :=
  dw (mu/2) Q (binaryHolevoBits (cowA (flaggedPair A) Q false) (cowA (flaggedPair A) Q true))
    (binaryHolevoBits (cowB (flaggedPair A) Q false) (cowB (flaggedPair A) Q true))

/-- PDF pp.6–7, (19)–(25): crossing-pair conditional ensemble. The source relation
j_prime = 1-k = a is built into both copies; the outer bits j,k_prime are averaged. -/
def crossCow {I : Type*} (A : PairData I) (Q : ℝ) (a : Bool) :
    Bool × Bool × Bool → Vec (I × I) :=
  fun z => (Real.sqrt ((if a = z.2.2 then 1-Q else Q)/4) : ℂ) •
    (if z.2.2 then tensor (A.v (z.1,!a)) (A.p (a,z.2.1) false)
      else tensor (A.p (z.1,!a) true) (A.v (a,z.2.1)))

/-- PDF p.7, (23): the Bob marginal sums over a, with b held fixed. -/
def crossCowB {I : Type*} (A : PairData I) (Q : ℝ) (b : Bool) :
    Bool × Bool × Bool → Vec (I × I) :=
  fun z => (Real.sqrt ((if z.2.2 = b then 1-Q else Q)/4) : ℂ) •
    (if b then tensor (A.v (z.1,!z.2.2)) (A.p (z.2.2,z.2.1) false)
      else tensor (A.p (z.1,!z.2.2) true) (A.v (z.2.2,z.2.1)))

/-- PDF p.7, (24),(25): correct crossing states rho_4^(a,a). -/
def crossCorrect {I : Type*} (A : PairData I) (a : Bool) : Bool × Bool → Vec (I × I) :=
  fun z => (1/2 : ℂ) •
    (if a then tensor (A.v (z.1,false)) (A.p (true,z.2) false)
      else tensor (A.p (z.1,true) true) (A.v (false,z.2)))

/-- PDF p.7, (42 analogue): the public alignment flag is retained by Eve. -/
def cowm1Info {I : Type*} [Fintype I] [DecidableEq I]
    (A : PairData I) (Q : ℝ) (bob : Bool) : ℝ :=
  if bob then (binaryHolevoBits (cowB A Q false) (cowB A Q true) +
    binaryHolevoBits (crossCowB A Q false) (crossCowB A Q true))/2
  else (binaryHolevoBits (cowA A Q false) (cowA A Q true) +
    binaryHolevoBits (crossCow A Q false) (crossCow A Q true))/2

/-- PDF p.7, (26): same-pair pure-state information plus crossing-pair Holevo. -/
def cowm1Leak {I : Type*} [Fintype I] [DecidableEq I]
    (A : PairData I) (Q : ℝ) : ℝ :=
  Q + (1-Q)/2 * (QAlgorithms.binEntropy2
    ((1+‖inner ℂ (A.p (true,false) false) (A.p (false,true) true)‖)/2) +
      binaryHolevoBits (crossCorrect A false) (crossCorrect A true))

/-- PDF p.7, (28): a repeated one-pulse ancilla assignment. -/
structure OneData (I : Type*) where
  v : Bool → Vec I
  p : Bool → Vec I

/-- PDF p.7, (29),(30): all one-pulse COWm2 Gram constraints. -/
def CowOneValid {I : Type*} [Fintype I] (A : OneData I) (mu V : ℝ) : Prop :=
  (∀ b, ‖A.v b‖ = 1 ∧ ‖A.p b‖ = 1) ∧
  inner ℂ (A.v false) (A.v true) = (Real.exp (-mu/2) : ℂ) ∧
  Complex.normSq (inner ℂ (A.v true) (A.p true)) = V

/-- PDF p.7: construct the free p_0 as an orthogonal error flag. -/
def flaggedOne {I : Type*} (A : OneData I) : OneData (Sum I (Fin 4)) where
  v := fun b => liftVec (A.v b)
  p := fun b => if b then liftVec (A.p true) else
    WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun j => if j = 0 then 1 else 0))

/-- PDF p.8, (31): product vectors for the two key pulses, from the same 1PA. -/
def oneToPair {I : Type*} (A : OneData I) : PairData (I × I) where
  v := fun x => tensor (A.v x.1) (A.v x.2)
  p := fun x b => if b then tensor (A.v x.1) (A.p x.2)
    else tensor (A.p x.1) (A.v x.2)

/-- PDF p.8, (34)–(39): all DPS 2PA vacuum/photon norms and monitored Gram data.
Here pulse-pair Booleans label signs, not occupancies. -/
def DpsValid {I : Type*} [Fintype I] (A : PairData I) (mu V : ℝ) : Prop :=
  (∀ x, ‖A.v x‖ = 1) ∧ (∀ x b, ‖A.p x b‖ = 1) ∧
  (∀ x y, inner ℂ (A.v x) (A.v y) =
    (Real.exp (-2*mu*(pairDistance x y : ℝ)) : ℂ)) ∧
  (∀ x, (inner ℂ (A.p x true) (A.p x false)).re = V) ∧
  (∀ x y, (inner ℂ (A.v x) (A.p x true) *
    inner ℂ (A.p y false) (A.v y)).re = V)

/-- PDF p.8, (34): normalized-ancilla, first-order Bob-sector array only. -/
def dpsOutput {I : Type*} (A : PairData I) (mu t : ℝ) (x : PulsePair) :
    Fin 3 → I → ℂ :=
  fun k i => if k = 0 then A.v x i else if k = 1 then
    dpsPhaseSign x.1 * (Real.sqrt (mu*t) : ℂ) * A.p x false i else
    dpsPhaseSign x.2 * (Real.sqrt (mu*t) : ℂ) * A.p x true i

/-- PDF p.9, Case 1: unnormalized interferometer ancilla vector. -/
def dps2Psi {I : Type*} (A : PairData I) (s w b : Bool) : Vec I :=
  dpsPhaseSign s • A.p (s,w) false + (dpsPhaseSign b * dpsPhaseSign w) • A.p (s,w) true

/-- PDF p.9, Case 2: crossing interference uses slots two and three. -/
def dps4Psi {I : Type*} (A : PairData I) (s w u v b : Bool) : Vec (I × I) :=
  dpsPhaseSign w • tensor (A.p (s,w) true) (A.v (u,v)) +
    (dpsPhaseSign b * dpsPhaseSign u) • tensor (A.v (s,w)) (A.p (u,v) false)

/-- PDF p.9: joint conditional block for Alice a, Bob b, same attacked pair. -/
def dps2Joint {I : Type*} (A : PairData I) (a b : Bool) : Bool → Vec I :=
  fun s => (Real.sqrt (1/8) : ℂ) • dps2Psi A s (Bool.xor s a) b

/-- PDF p.9: same-pair Alice marginal, retaining the factor 1/8. -/
def dps2A {I : Type*} (A : PairData I) (a : Bool) : Bool × Bool → Vec I :=
  fun z => (Real.sqrt (1/8) : ℂ) • dps2Psi A z.1 (Bool.xor z.1 a) z.2

/-- PDF p.9: same-pair Bob marginal. -/
def dps2B {I : Type*} (A : PairData I) (b : Bool) : Bool × Bool → Vec I :=
  fun z => (Real.sqrt (1/8) : ℂ) • dps2Psi A z.1 z.2 b

/-- PDF p.9: crossing-pair joint block with the factor 1/32. -/
def dps4Joint {I : Type*} (A : PairData I) (a b : Bool) :
    Bool × Bool × Bool → Vec (I × I) :=
  fun z => (Real.sqrt (1/32) : ℂ) •
    dps4Psi A z.1 z.2.1 (Bool.xor z.2.1 a) z.2.2 b

/-- PDF p.9: crossing Alice marginal; bit a is the relative sign of slots 2,3. -/
def dps4A {I : Type*} (A : PairData I) (a : Bool) :
    Bool × Bool × Bool × Bool → Vec (I × I) :=
  fun z => (Real.sqrt (1/32) : ℂ) •
    dps4Psi A z.1 z.2.1 (Bool.xor z.2.1 a) z.2.2.1 z.2.2.2

/-- PDF p.9: crossing Bob marginal. -/
def dps4B {I : Type*} (A : PairData I) (b : Bool) :
    Bool × Bool × Bool × Bool → Vec (I × I) :=
  fun z => (Real.sqrt (1/32) : ℂ) • dps4Psi A z.1 z.2.1 z.2.2.1 z.2.2.2 b

/-- PDF p.9, (42): Eve keeps the public same-pair/crossing-pair alignment flag. -/
def dpsInfo {I : Type*} [Fintype I] [DecidableEq I]
    (A : PairData I) (bob : Bool) : ℝ :=
  if bob then (binaryHolevoBits (dps2B A false) (dps2B A true) +
    binaryHolevoBits (dps4B A false) (dps4B A true))/2
  else (binaryHolevoBits (dps2A A false) (dps2A A true) +
    binaryHolevoBits (dps4A A false) (dps4A A true))/2

/-- PDF pp.9,12: balanced independent companion choice after a click. This is
exactly the source's one-half acceptance model, not an arbitrary schedule. -/
def bobPairLaw (P : Bool × Bool → ℝ) : (Bool × Bool) × Bool → ℝ :=
  fun z => P z.1 / 2

/-- Appendix A p.11: actual Z-channel joint law, q = nonempty fraction,
x = click probability conditional on a nonempty pulse. -/
def zLaw (q x : ℝ) : Bool × Bool → ℝ :=
  fun ab => if ab.1 then q*(if ab.2 then x else 1-x)
    else if ab.2 then 0 else 1-q

/-- Appendix A p.11: ideal mutual information from the actual channel law. -/
def zInfo (q x : ℝ) : ℝ := QAlgorithms.mutualInfoBits (zLaw q x)

/-- Appendix A p.11: coefficient of the small-click-probability information. -/
def zCoefficient (q : ℝ) : ℝ := -q*Real.log q / Real.log 2

/-- Appendix A pp.11–12: original COW, COWm1, COWm2, random consecutive
pairing, and Bob pairing, in that order. Nonempty fraction is one half; the
last two choices accept only mixed pairs. -/
def idealSiftingCoefficient (scheme : Fin 5) (mu : ℝ) : ℝ :=
  if scheme.val < 3 then mu/2 else
    mu/2 * (∑ x : Bool × Bool, if x.1 ≠ x.2 then (1/4:ℝ) else 0)

/-- Ideal sifted uniform bits are perfectly correlated; no security is asserted. -/
def idealBitLaw : Bool × Bool → ℝ := fun ab => if ab.1 = ab.2 then 1/2 else 0

/-- Appendix A p.11: joint on/off law restricted to announced slots. Every
click is kept, and the same fraction of no-click slots is selected independently
of Alice's input. f0 is the unconditional selected no-click fraction. -/
def announcedLaw (q x f0 : ℝ) : Bool × Bool → ℝ :=
  fun ab => zLaw q x ab * (if ab.2 then 1 else f0/(1-q*x))

example : keyPair false = (true,false) := rfl

example : errorIndex (false,false) true = 1 := rfl

/-- Real coordinate vector, used only for the paper's explicit appendix families. -/
def rvec {n : ℕ} (x : Fin n → ℝ) : Vec (Fin n) :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

/-- Coordinate basis vector; added flag dimensions are kept separate. -/
def basis {n : ℕ} (i : Fin n) : Vec (Fin n) :=
  WithLp.toLp 2 (fun j => if j = i then 1 else 0)

/-- Appendix B p.13, (B8): positive-regime correct-state overlap. -/
def cowMinimum (mu V : ℝ) : ℝ :=
  (2*V-1)*Real.exp (-mu) -
    2*Real.sqrt (V*(1-V))*Real.sqrt (1-(Real.exp (-mu))^2)

/-- Appendix B pp.12–13, (B4),(B5),(B8),(B9): explicit minimizing key
vectors and decoy completion. Error vectors will be added by flaggedPair. -/
def cowPositive (mu V : ℝ) : PairData (Fin 3) :=
  let g := Real.exp (-mu)
  let a := Real.sqrt ((1+g)/2)
  let b := Real.sqrt ((1-g)/2)
  let u := Real.sqrt (2*g/(1+g))
  let z := Real.sqrt ((1-g)/(1+g))
  let c := Real.sqrt (2*V/(1+V))*u + Real.sqrt ((1-V)/(1+V))*z
  let s := Real.sqrt (2*V/(1+V))*z - Real.sqrt ((1-V)/(1+V))*u
  let vac : PulsePair → Vec (Fin 3) := fun x =>
    if x = (true,false) then rvec ![a,b,0]
    else if x = (false,true) then rvec ![a,-b,0]
    else if x = (true,true) then rvec ![u,0,z] else basis 0
  let phot : PulsePair → Bool → Vec (Fin 3) := fun x slot =>
    if x = (true,false) ∧ slot = false then
      (Real.sqrt V : ℂ) • vac x - (Real.sqrt (1-V) : ℂ) • rvec ![b,-a,0]
    else if x = (false,true) ∧ slot = true then
      (Real.sqrt V : ℂ) • vac x - (Real.sqrt (1-V) : ℂ) • rvec ![b,a,0]
    else if x = (true,true) then rvec ![Real.sqrt ((1+V)/2)*c,
      (if slot then -1 else 1)*Real.sqrt ((1-V)/2), Real.sqrt ((1+V)/2)*s]
    else basis 0
  ⟨vac,phot⟩

/-- Appendix B p.13: a feasible zero-overlap construction, including V=0 and
V=1/2. The printed illustrative angle quotient is not used. The low-V branch
uses extra orthogonal residuals. The high-V branch solves the overlap equation
for its actual cosine; its denominator is positive in that branch. Decoy photon
residuals are independent of the key-vector residuals. -/
def cowZero (mu V : ℝ) : PairData (Fin 7) :=
  let g := Real.exp (-mu)
  let a := Real.sqrt ((1+g)/2)
  let b := Real.sqrt ((1-g)/2)
  let vac : PulsePair → Vec (Fin 7) := fun x =>
    if x = (true,false) then rvec ![a,b,0,0,0,0,0]
    else if x = (false,true) then rvec ![a,-b,0,0,0,0,0]
    else if x = (true,true) then
      rvec ![Real.sqrt (2*g/(1+g)),0,0,0,Real.sqrt ((1-g)/(1+g)),0,0]
    else basis 0
  let r := V*g/(1-V)
  let h := Real.sqrt (V*(1-V))*Real.sqrt (1-g^2)
  let c := (V*g-h)/((1-V)*g+h)
  let p0 := if V ≤ 1/2 then
      (Real.sqrt V : ℂ) • vac (true,false) + (Real.sqrt (1-V) : ℂ) • basis 2
    else (Real.sqrt V : ℂ) • vac (true,false) -
      (Real.sqrt (1-V)*c : ℂ) • rvec ![b,-a,0,0,0,0,0] +
      (Real.sqrt (1-V)*Real.sqrt (1-c^2) : ℂ) • basis 2
  let p1 := if V ≤ 1/2 then
      (Real.sqrt V : ℂ) • vac (false,true) +
      (Real.sqrt (1-V) : ℂ) • rvec ![0,0,-r,Real.sqrt (1-r^2),0,0,0]
    else (Real.sqrt V : ℂ) • vac (false,true) -
      (Real.sqrt (1-V) : ℂ) • rvec ![b,a,0,0,0,0,0]
  ⟨vac, fun x slot => if x = (true,false) ∧ slot = false then p0
    else if x = (false,true) ∧ slot = true then p1
    else if x = (true,true) then
      (Real.sqrt V : ℂ) • vac x + (Real.sqrt (1-V) : ℂ) • (if slot then basis 6 else basis 5)
    else basis 0⟩

/-- Appendix C p.14, (C2)–(C10): the displayed four-dimensional participating
vectors. The four unconstrained error states live in separately added dimensions.
The printed parenthetical identifying decoy photon vectors as orthogonal error
flags is corrected to the vacuum-input vectors specified in Section IV B. -/
def cowm1Family (mu V theta0 theta1 phi : ℝ) : PairData (Fin 4) :=
  let g := Real.exp (-mu)
  let a := Real.sqrt ((1+g)/2)
  let b := Real.sqrt ((1-g)/2)
  let u := Real.sqrt (2*g/(1+g))
  let z := Real.sqrt ((1-g)/(1+g))
  let vac : PulsePair → Vec (Fin 4) := fun x =>
    if x = (true,false) then rvec ![a,b,0,0]
    else if x = (false,true) then rvec ![a,-b,0,0]
    else if x = (false,false) then rvec ![u,0,z,0]
    else rvec ![u,0,-g*z,1-g]
  let perp0 := rvec ![b,-a,0,0]
  let perp1 := rvec ![b,a,0,0]
  let perpD1 := rvec ![0,0,Real.sqrt (1-g^2),g]
  let perpD2 := rvec ![z,0,g*u,-Real.sqrt (2*g)*Real.sqrt (1-g)]
  let w : PulsePair → Bool → Vec (Fin 4) := fun x slot =>
    if x = (true,false) then (Real.cos theta0 : ℂ) • perp0 +
      (Real.sin theta0*Real.cos theta1 : ℂ) • basis 2 +
      (Real.sin theta0*Real.sin theta1 : ℂ) • basis 3
    else if x = (false,true) then (Real.cos theta0 : ℂ) • perp1 +
      (Real.sin theta0*Real.cos theta1 : ℂ) • basis 2 +
      (Real.sin theta0*Real.sin theta1 : ℂ) • basis 3
    else (1/Real.sqrt 2 : ℂ) •
      ((Real.cos phi : ℂ) • perpD1 + (Real.sin phi : ℂ) • perpD2) +
      ((if slot then 1 else -1)/Real.sqrt 2 : ℂ) • basis 1
  ⟨vac,fun x slot => if errorSlot x slot then basis 0 else
    (Real.sqrt V : ℂ) • vac x - (Real.sqrt (1-V) : ℂ) • w x slot⟩

/-- Appendix D pp.14–15: minimum single-pulse overlap, including the zero regime. -/
def cowm2Minimum (mu V : ℝ) : ℝ :=
  if Real.exp (-mu) ≤ 1-V then 0 else
    Real.exp (-mu/2)*Real.sqrt V - Real.sqrt (1-Real.exp (-mu))*Real.sqrt (1-V)

/-- Appendix D p.15, (D3),(D4): piecewise witness without singular endpoint
angle quotients. p_0 is a fourth, independent coordinate outside the three
participating vectors. The V=0 branch is treated before the cosine quotient. -/
def cowm2Optimum (mu V : ℝ) : OneData (Fin 4) :=
  let s := Real.exp (-mu)
  let c := if V = 0 then 0 else if s ≤ 1-V then
    Real.sqrt (s*V/((1-s)*(1-V))) else 1
  ⟨(fun b => if b then basis 0 else
      rvec ![Real.exp (-mu/2),Real.sqrt (1-s),0,0]),
   (fun b => if b then rvec ![Real.sqrt V,-Real.sqrt (1-V)*c,
      Real.sqrt (1-V)*Real.sqrt (1-c^2),0] else basis 3)⟩

/-- Appendix E p.16, (E1)–(E3): normalized leading-order DPS one-pulse data.
All sign-conditioned visibilities are checked separately. -/
def DpsOneValid {I : Type*} [Fintype I] (A : OneData I) (mu V : ℝ) : Prop :=
  (∀ s, ‖A.v s‖ = 1 ∧ ‖A.p s‖ = 1) ∧
  inner ℂ (A.v false) (A.v true) = (Real.exp (-2*mu) : ℂ) ∧
  (∀ s w, (inner ℂ (A.v s) (A.p s) * inner ℂ (A.p w) (A.v w)).re = V)

/-- Appendix E p.16: actual product ancilla after the DPS interferometer. -/
def dps1Psi {I : Type*} (A : OneData I) (s w b : Bool) : Vec (I × I) :=
  dpsPhaseSign s • tensor (A.p s) (A.v w) +
    (dpsPhaseSign b*dpsPhaseSign w) • tensor (A.v s) (A.p w)

/-- Appendix E p.16: subnormalized block rho^(a,b), with the source's factor 1/8. -/
def dps1Joint {I : Type*} (A : OneData I) (a b : Bool) : Bool → Vec (I × I) :=
  fun s => (Real.sqrt (1/8) : ℂ) • dps1Psi A s (Bool.xor s a) b

/-- Appendix E p.16: Alice marginal, summing Bob's outcome. -/
def dps1A {I : Type*} (A : OneData I) (a : Bool) : Bool × Bool → Vec (I × I) :=
  fun z => (Real.sqrt (1/8) : ℂ) • dps1Psi A z.1 (Bool.xor z.1 a) z.2

/-- Appendix E p.16: Bob marginal, correctly summing Alice's bit a.
Printed: a sum over b while b remains free. Changed: sum over a, as required
by conditional marginalization and the matching construction on p.9. -/
def dps1B {I : Type*} (A : OneData I) (b : Bool) : Bool × Bool → Vec (I × I) :=
  fun z => (Real.sqrt (1/8) : ℂ) • dps1Psi A z.1 (Bool.xor z.1 z.2) b

/-- Appendix E pp.16–17, (E5)–(E8): the complete six-parameter family.
The half-angle phases and the relative minus sign in w_minus are retained. -/
def dpsOneFamily (mu V : ℝ) (thetaS phiS : Bool → ℝ) (theta phi : ℝ) :
    OneData (Fin 4) :=
  let g := Real.exp (-2*mu)
  let a := Real.sqrt ((1+g)/2)
  let b := Real.sqrt ((1-g)/2)
  let vac := fun s : Bool => rvec ![a,(if s then -1 else 1)*b,0,0]
  let perp := fun s : Bool => rvec ![b,-(if s then -1 else 1)*a,0,0]
  let w := fun s : Bool => WithLp.toLp 2
    ![(0:ℂ),0,(Real.cos (theta/2) : ℂ)*phase ((if s then -1 else 1)*phi/2),
      dpsPhaseSign s*(Real.sin (theta/2) : ℂ)*phase ((if s then -1 else 1)*phi/2)]
  ⟨vac,fun s => (Real.sqrt V : ℂ) • vac s -
    ((Real.sqrt (1-V)*Real.cos (thetaS s) : ℂ)*phase (phiS s)) • perp s -
    (Real.sqrt (1-V)*Real.sin (thetaS s) : ℂ) • w s⟩

/-- All four one-pulse vectors, with a common photon phase gauge. -/
def oneFamilyVectors {I : Type*} (A : OneData I) (z : ℂ) : Bool × Bool → Vec I :=
  fun x => if x.1 then z • A.p x.2 else A.v x.2

/-- Equality of finite vector geometry, explicitly witnessed by an isometry
of their spans. This preserves every constructed conditional operator spectrum. -/
def SameSpanGeometry {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (x : I → H) (y : I → K) : Prop :=
  ∃ U : Submodule.span ℂ (Set.range x) ≃ₗᵢ[ℂ] Submodule.span ℂ (Set.range y),
    ∀ i, U ⟨x i,Submodule.subset_span (Set.mem_range_self i)⟩ =
      ⟨y i,Submodule.subset_span (Set.mem_range_self i)⟩

/-- Appendix E p.17, (E11): exact symmetric vacuum vectors, embedded in six
real coordinates. The third/fourth coordinates are sqrt((1-gamma^2)/2). -/
def dpsRestrictedVacuum (mu : ℝ) (x : PulsePair) : Vec (Fin 6) :=
  let g := Real.exp (-2*mu)
  let c := Real.sqrt ((1-g^2)/2)
  rvec ![(1+g)/2,(if x.1 = x.2 then 1 else -1)*(1-g)/2,
    (if x.1 = x.2 then (if x.1 then -c else c) else 0),
    (if x.1 = x.2 then 0 else (if x.1 then -c else c)),0,0]

/-- Appendix E p.17, (E13),(E14): actual photon vectors are constructed from
unit auxiliary data; their normalization and visibility are conclusions below. -/
def dpsRestricted (mu V : ℝ) (w : PulsePair → Bool → Vec (Fin 6)) : PairData (Fin 6) :=
  ⟨dpsRestrictedVacuum mu,fun x b =>
    (Real.sqrt V : ℂ) • dpsRestrictedVacuum mu x - (Real.sqrt (1-V) : ℂ) • w x b⟩

/-- Section IV E p.9: the long-distance COW BSA information. -/
def cowIdealLeak (mu : ℝ) : ℝ := QAlgorithms.binEntropy2 ((1-Real.exp (-mu))/2)

/-- Section IV E p.9 and Appendix E pp.17–18: long-distance DPS BSA information. -/
def dpsIdealLeak (mu : ℝ) : ℝ :=
  2*QAlgorithms.binEntropy2 ((1-Real.exp (-2*mu))/2) -
    QAlgorithms.binEntropy2 ((1-Real.exp (-4*mu))/2)

example (mu V : ℝ) (w : PulsePair → Bool → Vec (Fin 6)) (x : PulsePair) (b : Bool) :
    (dpsRestricted mu V w).p x b = (Real.sqrt V : ℂ) • dpsRestrictedVacuum mu x -
      (Real.sqrt (1-V) : ℂ) • w x b := rfl

example : pairDistance (true,false) (false,true) = 2 := rfl

example {I : Type*} [Fintype I] (v w : Vec I) :
    ancillaGram (fun b : Bool => if b then w else v) false true = inner ℂ v w := rfl

example {I J : Type*} (v : Vec I) (w : Vec J) (i : I) (j : J) :
    tensor v w (i,j) = v i * w j := rfl

end QAlgorithms.Papers.Independent.Intake100.P92


