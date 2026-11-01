-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P87
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:14:29.086983+00:00
-- url     : https://prove2.me/theorems/8c1751d4-4455-4d15-8a3c-a343a1e0dcd4
-- title:
--   Definitions for Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances
-- statement:
--   The objects the formalized statements of *Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances* (arXiv:quant-ph/9803006) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `basisPinch`: PDF p.4: complete nonselective measurement in the columns of U.
--   - `coarseProjector`: PDF p.4: spectral projector of a coarse observable diagonal in U.
--   - `sequentialLaw`: PDF p.4: the full sequential Lueders joint law, with the first test acting first.
--   - `PairRegister`: PDF pp.4,8: bipartite N-pair computational index, Alice register first.
--   - `sourceBellPaulis`: PDF p.8, (1)--(3): translate the paper's phase/parity bits to the accepted phase-free Pauli labels. I,X,Z,Y correspond to 00,01,10,11. The imported Bell vector for Y is i times the paper's singlet; Bell projectors are unchanged by this phase.
--   - `singletKet`: PDF p.4: the N-singlet vector from the accepted Bell construction. Multiplication by (-i)^N fixes the source's positive |01> amplitude per pair. This is a phase/label adapter, not a second Bell-vector definition.
--   - `bellPinch`: PDF pp.8--10,21: virtual complete N-Bell premeasurement, with outcome forgotten.
--   - `singletOverlap`: PDF pp.4,14--15,19: squared singlet overlap, not root fidelity.
--   - `OutcomePartition`: PDF p.19: finite measurable coarse grainings; empty cells are allowed.
--   - `partitionLaw`: PDF p.19: joint Born probabilities for two local generalized measurements.
--   - `measuredInfo`: PDF p.19: Shannon information for arbitrary measurable outcomes, defined as an extended nonnegative supremum over all finite measurable coarse grainings.
--   - `axisEffect`: PDF p.4: a measurement basis for a common spin axis, lifted to R local qubits.
--   - `idealKeyLaw`: PDF p.4: all four local outcomes per pair and an arbitrary Eve event.
--   - `keyPartitionLaw`: PDF pp.14--15: key/Eve joint law; Bob's outcomes are not disclosed.
--   - `keyLeakage`: PDF pp.14--15: classical Shannon information for a fixed arbitrary Eve measurement.
--   - `directMissProbability`: PDF p.7: exact failure event of direct sampling, one fixed nonsinglet position.
--   - `hashingCollisionProbability`: PDF p.7: uniform independent fair (nonzero-mask) parity questions.
--   - `spectralContribution`: PDF p.21: entropy contribution of a spectral subset of a probability vector.
--   - `axisPauli`: PDF pp.20--21: Pauli axes x,y,z, respectively.
--   - `pairAxisProjector`: PDF pp.20--21: coarse antiparallel/parallel projectors for one pair. The outcome true means antiparallel.
--   - `atPair`: PDF pp.20--21: lift a two-qubit operator to a named pair, identities on other pairs.
--   - `pairAxisSampleLaw`: PDF pp.20--21: executed sequential coarse measurements on distinct named pairs. There is exactly one axis for each sampled pair, not three counterfactual measurements.
--   - `singletEstimate`: PDF p.21: the estimator (3k-m)/(2m), in real arithmetic and without clipping. Only m>0 is used in the estimation theorem.
--   - `meanSingletEstimate`: PDF pp.20--21: uniform m distinct positions, independent uniform axes and Born outcomes. Ordered injections give the same sampling law as uniform subsets with an ordering.
--   - `meanLocalSingletWeight`: PDF pp.11,20--21: expected singlet fraction, the mean of local singlet projectors.
--   - `bb84SignalKet`: PDF pp.14,19: the four BB84 one-photon polarization states. The basis bit selects z (false) or x (true); it is independent of photon number.
--   - `photonPulse`: PDF p.19: an already supplied n-photon identically polarized pulse. This is a tensor power of the input polarization, not a physical cloning operation.
--   - `extractedPulse`: PDF p.19: ideal number-resolved extraction is the fixed tensor-factor split. For n+1 photons, Eve stores the first and Bob receives the remaining n.
--   - `matchedPolarizationProb`: PDF p.19: matched-basis polarization measurement after the basis announcement.
--   - `poissonMass`: PDF pp.14,19: Poisson photon statistics, with no finite cutoff.
--   - `pnsForwardRate`: PDF p.19: available genuine-click rate, forwarding only multiphoton pulses. Number n+2 leaves n+1 photons at Bob, so d is evaluated at n+1.
--   - `pnsKeyLaw`: PDF p.19: subnormalized sifted two-bit law of the explicit number-measure, extract/store, superior-channel forwarding and basis-delayed measurement attack. Blocked pulses produce no transmitted key signal. Bob's click response d is basis-independent. The classical thinning probability t is independent of polarization.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, https://arxiv.org/abs/quant-ph/9803006v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_FreshCopyTomographyPrograms

/-!
Lo and Chau, arXiv:quant-ph/9803006v5. PDF page numbers throughout.
Only statements are admitted. Local definitions have complete bodies.
Deferred protocol results and cited background are recorded in HARD.md.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate
open QAlgorithms.Measurements

/-- PDF p.4: complete nonselective measurement in the columns of U. -/
def basisPinch {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  (U : Matrix I I ℂ) *
    Matrix.diagonal (fun i => ((U : Matrix I I ℂ)ᴴ * rho * (U : Matrix I I ℂ)) i i) *
      (U : Matrix I I ℂ)ᴴ

/-- PDF p.4: spectral projector of a coarse observable diagonal in U. -/
def coarseProjector {I O : Type*} [Fintype I] [DecidableEq I] [DecidableEq O]
    (U : Matrix.unitaryGroup I ℂ) (f : I → O) (o : O) : Matrix I I ℂ :=
  (U : Matrix I I ℂ) * Matrix.diagonal (fun i => if f i = o then 1 else 0) *
    (U : Matrix I I ℂ)ᴴ

/-- PDF p.4: the full sequential Lueders joint law, with the first test acting first. -/
def sequentialLaw {I O : Type*} [Fintype I] [DecidableEq I] [DecidableEq O]
    {t : ℕ} (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ)
    (f : Fin t → I → O) (o : Fin t → O) : ℝ :=
  let K := orderedProd (fun j => coarseProjector U (f j) (o j))
  (K * rho * Kᴴ).trace.re

example {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ) :
    sequentialLaw U rho (t := 0) (O := Bool) Fin.elim0 Fin.elim0 = rho.trace.re := by
  simp [sequentialLaw, orderedProd]

/-- PDF pp.4,8: bipartite N-pair computational index, Alice register first. -/
abbrev PairRegister (N : ℕ) := Qubits N × Qubits N

/-- PDF p.8, (1)--(3): translate the paper's phase/parity bits to the
accepted phase-free Pauli labels. I,X,Z,Y correspond to 00,01,10,11.
The imported Bell vector for Y is i times the paper's singlet; Bell projectors
are unchanged by this phase. -/
def sourceBellPaulis {N : ℕ} (w : PairRegister N) : DopedTomography.BellLabel N :=
  fun i => if w.1 i then
    (if w.2 i then Stabilizer.Pauli.Y else Stabilizer.Pauli.Z)
  else (if w.2 i then Stabilizer.Pauli.X else Stabilizer.Pauli.I)

/-- PDF p.4: the N-singlet vector from the accepted Bell construction.
Multiplication by (-i)^N fixes the source's positive |01> amplitude per pair.
This is a phase/label adapter, not a second Bell-vector definition. -/
def singletKet (N : ℕ) : EuclideanSpace ℂ (PairRegister N) :=
  (-Complex.I) ^ N • DopedTomography.bellVector (fun _ : Fin N => Stabilizer.Pauli.Y)

/-- PDF pp.8--10,21: virtual complete N-Bell premeasurement, with outcome forgotten. -/
def bellPinch {N : ℕ} (rho : Matrix (PairRegister N) (PairRegister N) ℂ) :
    Matrix (PairRegister N) (PairRegister N) ℂ :=
  ∑ w : PairRegister N, DopedTomography.bellInstrument (sourceBellPaulis w) * rho *
    DopedTomography.bellInstrument (sourceBellPaulis w)

example : sourceBellPaulis (N := 1) (fun _ => true, fun _ => true) 0 =
    Stabilizer.Pauli.Y := rfl

example : sourceBellPaulis (N := 1) (fun _ => false, fun _ => true) 0 =
    Stabilizer.Pauli.X := rfl

/-- PDF pp.4,14--15,19: squared singlet overlap, not root fidelity. -/
def singletOverlap {N : ℕ} (rho : Matrix (PairRegister N) (PairRegister N) ℂ) : ℝ :=
  effectProb (pureDensity (singletKet N)) rho

/-- PDF p.19: finite measurable coarse grainings; empty cells are allowed. -/
structure OutcomePartition (O : Type*) [MeasurableSpace O] (n : ℕ) where
  label : O → Fin n
  measurable : Measurable label

/-- PDF p.19: joint Born probabilities for two local generalized measurements. -/
def partitionLaw {A B X Y : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [MeasurableSpace X] [MeasurableSpace Y]
    (rho : Matrix (A × B) (A × B) ℂ) (P : OperatorPOVM A X) (Q : OperatorPOVM B Y)
    {n m : ℕ} (f : OutcomePartition X n) (g : OutcomePartition Y m)
    (z : Fin n × Fin m) : ℝ :=
  effectProb (Matrix.kronecker (P.operator {x | f.label x = z.1})
    (Q.operator {y | g.label y = z.2})) rho

/-- PDF p.19: Shannon information for arbitrary measurable outcomes, defined as
an extended nonnegative supremum over all finite measurable coarse grainings. -/
def measuredInfo {A B X Y : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [MeasurableSpace X] [MeasurableSpace Y]
    (rho : Matrix (A × B) (A × B) ℂ) (P : OperatorPOVM A X) (Q : OperatorPOVM B Y) : ENNReal :=
  ⨆ (n : ℕ) (m : ℕ) (f : OutcomePartition X n) (g : OutcomePartition Y m),
    ENNReal.ofReal (mutualInfoBits (partitionLaw rho P Q f g))

example {X : Type*} [MeasurableSpace X] :
    OutcomePartition X 1 := ⟨fun _ => 0, measurable_const⟩

/-- PDF p.4: a measurement basis for a common spin axis, lifted to R local qubits. -/
def axisEffect (R : ℕ) (U : Matrix.unitaryGroup Bool ℂ) (a : Qubits R) :
    Matrix (Qubits R) (Qubits R) ℂ :=
  fun x y => ∏ i, (U : Matrix Bool Bool ℂ) (x i) (a i) *
    conj ((U : Matrix Bool Bool ℂ) (y i) (a i))

/-- PDF p.4: all four local outcomes per pair and an arbitrary Eve event. -/
def idealKeyLaw {E Y : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace Y]
    {R : ℕ} (rho : Matrix (PairRegister R × E) (PairRegister R × E) ℂ)
    (U : Matrix.unitaryGroup Bool ℂ) (Q : OperatorPOVM E Y)
    (a b : Qubits R) (S : Set Y) : ℝ :=
  effectProb (Matrix.kronecker (Matrix.kronecker (axisEffect R U a) (axisEffect R U b))
    (Q.operator S)) rho

/-- PDF pp.14--15: key/Eve joint law; Bob's outcomes are not disclosed. -/
def keyPartitionLaw {E Y : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace Y]
    {R : ℕ} (rho : Matrix (PairRegister R × E) (PairRegister R × E) ℂ)
    (U : Matrix.unitaryGroup Bool ℂ) (Q : OperatorPOVM E Y)
    {m : ℕ} (g : OutcomePartition Y m) (z : Qubits R × Fin m) : ℝ :=
  effectProb (Matrix.kronecker (Matrix.kronecker (axisEffect R U z.1) 1)
    (Q.operator {y | g.label y = z.2})) rho

/-- PDF pp.14--15: classical Shannon information for a fixed arbitrary Eve measurement. -/
def keyLeakage {E Y : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace Y]
    {R : ℕ} (rho : Matrix (PairRegister R × E) (PairRegister R × E) ℂ)
    (U : Matrix.unitaryGroup Bool ℂ) (Q : OperatorPOVM E Y) : ENNReal :=
  ⨆ (m : ℕ) (g : OutcomePartition Y m),
    ENNReal.ofReal (mutualInfoBits (keyPartitionLaw rho U Q g))

/-- PDF p.7: exact failure event of direct sampling, one fixed nonsinglet position. -/
def directMissProbability (N m : ℕ) (bad : Fin N) : ℝ :=
  let samples := (Finset.univ : Finset (Fin N)).powersetCard m
  ((samples.filter (fun S => bad ∉ S)).card : ℝ) / samples.card

/-- PDF p.7: uniform independent fair (nonzero-mask) parity questions. -/
def hashingCollisionProbability {N : ℕ} (m : ℕ) (x y : Qubits N) : ℝ := by
  classical
  exact (((Finset.univ : Finset (Fin m → {s : Qubits N // s ≠ fun _ => false})).filter
    (fun ss => ∀ i, dotBits x (ss i).val = dotBits y (ss i).val)).card : ℝ) /
      Fintype.card (Fin m → {s : Qubits N // s ≠ fun _ => false})

example (x y : Qubits 1) : hashingCollisionProbability 0 x y = 1 := by
  simp [hashingCollisionProbability]

/-- PDF p.21: entropy contribution of a spectral subset of a probability vector. -/
def spectralContribution {I : Type*} [Fintype I] (p : I → ℝ) (S : Finset I) : ℝ :=
  ∑ i ∈ S, -p i * Real.logb 2 (p i)

example {I : Type*} [Fintype I] (p : I → ℝ) : spectralContribution p ∅ = 0 := by
  simp [spectralContribution]

/-- PDF pp.20--21: Pauli axes x,y,z, respectively. -/
def axisPauli (k : Fin 3) : Matrix Bool Bool ℂ :=
  if k = 0 then pauliX else if k = 1 then pauliY else pauliZ

/-- PDF pp.20--21: coarse antiparallel/parallel projectors for one pair.
The outcome true means antiparallel. -/
def pairAxisProjector (k : Fin 3) (anti : Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (1 / 2 : ℂ) • (1 + (if anti then (-1 : ℂ) else 1) •
    Matrix.kronecker (axisPauli k) (axisPauli k))

/-- PDF pp.20--21: lift a two-qubit operator to a named pair, identities on other pairs. -/
def atPair {N : ℕ} (i : Fin N) (P : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix (PairRegister N) (PairRegister N) ℂ := by
  classical
  exact fun x y => P (x.1 i, x.2 i) (y.1 i, y.2 i) *
    ∏ j ∈ Finset.univ.erase i,
      if x.1 j = y.1 j ∧ x.2 j = y.2 j then (1 : ℂ) else 0

/-- PDF pp.20--21: executed sequential coarse measurements on distinct named pairs.
There is exactly one axis for each sampled pair, not three counterfactual measurements. -/
def pairAxisSampleLaw {N m : ℕ} (rho : Matrix (PairRegister N) (PairRegister N) ℂ)
    (s : Fin m ↪ Fin N) (axes : Fin m → Fin 3) (anti : Qubits m) : ℝ :=
  let K := orderedProd (fun j => atPair (s j) (pairAxisProjector (axes j) (anti j)))
  (K * rho * Kᴴ).trace.re

/-- PDF p.21: the estimator (3k-m)/(2m), in real arithmetic and without clipping.
Only m>0 is used in the estimation theorem. -/
def singletEstimate (m : ℕ) (anti : Qubits m) : ℝ :=
  (3 * (Finset.univ.filter (fun j => anti j = true)).card - (m : ℝ)) / (2 * m)

/-- PDF pp.20--21: uniform m distinct positions, independent uniform axes and Born outcomes.
Ordered injections give the same sampling law as uniform subsets with an ordering. -/
def meanSingletEstimate {N : ℕ}
    (rho : Matrix (PairRegister N) (PairRegister N) ℂ) (m : ℕ) : ℝ :=
  (∑ s : Fin m ↪ Fin N, ∑ axes : Fin m → Fin 3, ∑ anti : Qubits m,
    pairAxisSampleLaw rho s axes anti * singletEstimate m anti) /
      ((Fintype.card (Fin m ↪ Fin N) : ℝ) * (3 : ℝ) ^ m)

/-- PDF pp.11,20--21: expected singlet fraction, the mean of local singlet projectors. -/
def meanLocalSingletWeight {N : ℕ}
    (rho : Matrix (PairRegister N) (PairRegister N) ℂ) : ℝ :=
  (∑ i : Fin N, effectProb (atPair i (pureDensity
    (WithLp.toLp 2 (fun x : Bool × Bool =>
      singletKet 1 (fun _ => x.1, fun _ => x.2))))) rho) / N

example : singletEstimate 1 (fun _ => false) = -(1 / 2 : ℝ) := by
  norm_num [singletEstimate]

/-- PDF pp.14,19: the four BB84 one-photon polarization states.
The basis bit selects z (false) or x (true); it is independent of photon number. -/
def bb84SignalKet (basis bit : Bool) : EuclideanSpace ℂ Bool :=
  if basis then act hadamard (ket bit) else ket bit

/-- PDF p.19: an already supplied n-photon identically polarized pulse.
This is a tensor power of the input polarization, not a physical cloning operation. -/
def photonPulse (n : ℕ) (basis bit : Bool) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 (fun x => ∏ i, bb84SignalKet basis bit (x i))

/-- PDF p.19: ideal number-resolved extraction is the fixed tensor-factor split.
For n+1 photons, Eve stores the first and Bob receives the remaining n. -/
def extractedPulse (n : ℕ) (basis bit : Bool) :
    EuclideanSpace ℂ (Bool × Qubits n) :=
  WithLp.toLp 2 (fun x => photonPulse (n + 1) basis bit (Fin.cons x.1 x.2))

/-- PDF p.19: matched-basis polarization measurement after the basis announcement. -/
def matchedPolarizationProb (basis bit outcome : Bool) : ℝ :=
  Complex.normSq (inner ℂ (bb84SignalKet basis outcome) (bb84SignalKet basis bit))

/-- PDF pp.14,19: Poisson photon statistics, with no finite cutoff. -/
def poissonMass (mu : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-mu) * mu ^ n / (Nat.factorial n : ℝ)

example : poissonMass 0 0 = 1 := by
  simp [poissonMass]

/-- PDF p.19: available genuine-click rate, forwarding only multiphoton pulses.
Number n+2 leaves n+1 photons at Bob, so d is evaluated at n+1. -/
def pnsForwardRate (p d : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, p (n + 2) * d (n + 1)

/-- PDF p.19: subnormalized sifted two-bit law of the explicit number-measure,
extract/store, superior-channel forwarding and basis-delayed measurement attack.
Blocked pulses produce no transmitted key signal. Bob's click response d is
basis-independent. The classical thinning probability t is independent of polarization. -/
def pnsKeyLaw (p d : ℕ → ℝ) (t : ℝ) (basis bit bob eve : Bool) : ℝ :=
  ∑' n : ℕ, t * p (n + 2) * d (n + 1) *
    matchedPolarizationProb basis bit bob * matchedPolarizationProb basis bit eve

end QAlgorithms.Papers.Independent.Intakenext100.P87


