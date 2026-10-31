-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93
-- name    : QAlgorithms_Papers_Independent_Intake100_P93
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:34:23.63363+00:00
-- url     : https://prove2.me/theorems/bbac4db8-1a14-467b-9536-b851135d88ec
-- title:
--   Definitions for Entanglement of assistance and multipartite state distillation
-- statement:
--   The objects the formalized statements of *Entanglement of assistance and multipartite state distillation* (arXiv:quant-ph/0505038) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SState`
--   - `AssistanceBasis`
--   - `stateCoordinates`: PDF pp.1--2: a bundled state expressed in a prescribed local basis.
--   - `RepresentsState`: PDF pp.1--2: equality of the physical state and every local dimension.
--   - `groupedStateCopies`: PDF pp.1--3: n i.i.d. copies, grouped only within each party.
--   - `partyMarginal`: PDF pp.2,7: partial trace onto a specified group of distinct parties.
--   - `partyEntropy`: PDF pp.1--2: entropy of the actual reduced state.
--   - `pairMarginal`: PDF pp.2--3: ordered two-party marginal; all other factors are traced out.
--   - `cutMinimum`: PDF pp.2,7: all cuts separating a from b, including both extreme cuts. The finite index set is nonempty even when there are no helpers.
--   - `InstrumentAt`: PDF pp.1,7: the accepted local Kraus-instrument relation with its acting party exposed. This is precisely P33.LocalInstrument with that witness fixed; its lifted Kraus operators act as the identity at every other party.
--   - `ChannelAt`: PDF pp.1,5--6: a local channel without an outgoing public outcome.
--   - `MixesTo`: PDF p.1: unconditional output, retaining every branch's probability.
--   - `RestrictedLocalTree`: PDF pp.1,7: finite adaptive LOCC with only parties in allowed acting. Every local instrument is complete; there are no quantum messages or supplied entangled ancillas. Classical outcomes may select any later local instrument.
--   - `HelperTree`: PDF pp.2,7--8: each remaining helper has exactly one measurement turn, then discards its quantum system and broadcasts its outcome. Later helpers may depend on earlier messages. A and B may finally use ordinary two-way LOCC.
--   - `HelperBroadcast`: PDF pp.2,5--6: one helper instrument, one broadcast, then two local message-dependent channels. The helper keeps its quantum output; local helper postprocessing is absorbed into its instrument. No feedback or A--B messages.
--   - `AssistanceProtocol`: PDF pp.1--2,5--7: the three distinct protocol classes.
--   - `AssistanceConverts`: PDF pp.1--2,5--7: physical conversion, without postselection.
--   - `targetDims`: PDF pp.1--2: g shared cat bits and e Bell bits on edge a--b. At zero counts every local output has dimension one. In applications g>0 only for m=3.
--   - `bellGhzTarget`: PDF pp.1--2: the exact joint GHZ^g tensor Bell^e ket, locally regrouped. The coefficient and the shared labels fix relative signs and normalization.
--   - `DistillationBlock`: PDF pp.1--2: a finite-block code with one joint target fidelity test. Input is exactly n i.i.d. copies; all other quantum outputs are disposed of.
--   - `AssistedYield`: PDF pp.1--2: eventual positive-blocklength rate closure. Real rates are nonnegative; integer output counts may be zero. Epsilon controls joint fidelity and delta controls both rates. Algorithms are chosen before any measurement outcome. No input-dependent extra resource is supplied.
--   - `averageEntanglement`: PDF p.3: ensemble average entanglement across the displayed bipartition.
--   - `assistance`: PDF p.3: one-copy assistance, optimized over all finite normalized pure ensembles. On density inputs the set is nonempty and bounded in [0,min(log2 d_A,log2 d_B)]; invalid-input defaults are never used.
--   - `purificationPairEquiv`: PDF p.3: a fixed local basis identification for the purifying register.
--   - `tripartitePurification`: PDF pp.2--3: C holds the canonical purification of the given AB density; it is not an independently chosen resource. All purifications give the same operational rate up to a local isometry on C.
--   - `operationalAssistance`: PDF p.3: operational EPR yield of the purification, defined independently of the ensemble roof and its regularization. The rate set contains zero and is bounded for every physical finite-dimensional state.
--   - `assistanceSequence`: PDF p.3: n indexes n+1 copies, never a division by zero.
--   - `determinantVector`: PDF p.3, Example 4: the six signed determinant-state amplitudes.
--   - `determinantMarginal`: PDF p.3, Example 4: the actual two-qutrit reduction.
--   - `antisymmetricPairAmplitude`: PDF p.3, Example 4: an unnormalized antisymmetric two-qutrit ket.
--   - `superadditiveWitness`: PDF p.3, Example 4: PLUS of two orthogonal tensor products, coefficient 1/sqrt(8); grouped as A1A2:B1B2.
--   - `witnessOrbit`: PDF p.3, Example 4: the orbit preserves each copy's antisymmetric subspace.
--   - `upsilonVector`: PDF p.6, Example 10: alpha|0>Phi+ + beta|1>Phi-, with positive Bell phase on |00> and opposite phases on |11>. Parameters are real as in the source.
--   - `symmetricWKet`: PDF pp.6--7, Example 11: normalized W ket.
--   - `choiKet`: PDF p.8, Section VII: normalized maximally entangled input, trace one.
--   - `dimensionedDilationPower`: PDF pp.4--5: the memoryless isometric channel to Bob and the helper's environment, with each party's n systems regrouped locally.
--   - `transmissionState`: PDF p.5: after encoding one half of a Bell test state, apply U^tensor n only to the transmitted register. Parties are Alice's memory, Bob, Charlie, and an UNTOUCHED external reference, in that order. The initial reference entanglement is local to the sender's test input, not a supplied A--B resource.
--   - `TransmissionBlock`: PDF pp.4--5, Theorem 8: an actual n-use transmission code. The reference (party 3) is excluded from every local operation. With unlimited=false there is only C's instrument and one broadcast followed by Alice/Bob local channels; with unlimited=true all three honest parties may use adaptive LOCC. Arbitrary local encoder memory is allowed and all work is discarded in the final Bell test. No preshared honest-party entanglement or quantum side message occurs.
--   - `TransmissionRate`: PDF pp.4--5: environment-assisted quantum communication rates, evaluated on the full purifying-reference Bell test, for all sufficiently large positive n.
--   - `assistedCapacityObjective`: PDF p.5, Theorem 8: optimization over normalized input density matrices. The value set is nonempty and bounded on positive-dimensional channels.
--   - `RandomnessCode`: PDF p.6, proof of Theorem 9: a one-way-broadcast common-randomness code. X is the ENTIRE public message. C also keeps a private k-bit output, while A and B use X-dependent local POVMs with private outputs. All branches are included. This POVM form includes arbitrary local ancillary randomness and private postprocessing. No private outcome is silently made public.
--   - `randomnessLaw`: PDF p.6: joint law of the public message and all three private strings, computed from the product local effects on the actual shared state.
--   - `randomnessError`: PDF p.6: total variation from Uniform(identical k-bit strings) times law(X). Keeping X is essential: broadcasting fresh random bits alone fails.
--   - `RandomnessRate`: PDF p.6: independent shared randomness at an eventual i.i.d. rate; the total-variation error tests uniformity, agreement, AND transcript independence.
--   - `HighEntropyEnsemble`: PDF p.9: a nearby pure-state ensemble, every component having entropy at least n(rate-delta). Approximation is in trace norm, not channel norm and not a componentwise fidelity to maximally entangled vectors.
--   - `TypicalHighEntropyEnsemble`: PDF p.9: local typical-subspace consequence, expressed by actual local isometric embeddings. The compressed state is the normalized local projection of rho^tensor n; the positive projection weight prevents division by zero. Both the discarded-subspace error and the ensemble error are retained. Logarithmic local dimensions approximate n times the respective marginal entropies. These are subspace isometries, never full-input channel isometries.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, https://arxiv.org/abs/quant-ph/0505038v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

/-! Smolin--Verstraete--Winter, quant-ph/0505038v1. Finite dimensions;
all logarithms and entropies are in bits. Compilation is pending batch handoff.
Only accepted library modules are imported. Distinct assistance interfaces are paper-local.
Generic short-name collisions are distinguished by descriptive names; exact
operator, ensemble, tensor-product, channel and Choi primitives are imported. -/

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.
open Information100.P21 (Op)
open Information100.P08 (PureEnsemble)
open Dependency50.P07 (bipartiteProduct)
open Information100.P67 (receiverChannel)
open Support50.P11 (choiState)

abbrev SState := Claimed50.P33.FiniteState

abbrev AssistanceBasis {m : ℕ} (d : Fin m → ℕ) := (i : Fin m) → Fin (d i)

/-- PDF pp.1--2: a bundled state expressed in a prescribed local basis. -/
def stateCoordinates {m : ℕ} (s : SState m) (d : Fin m → ℕ) : Op (AssistanceBasis d) :=
  fun x y => Claimed50.P33.stateEntry s (fun i => (x i).val) (fun i => (y i).val)

/-- PDF pp.1--2: equality of the physical state and every local dimension. -/
def RepresentsState {m : ℕ} (s : SState m) (d : Fin m → ℕ) (rho : Op (AssistanceBasis d)) : Prop :=
  s.dims = d ∧ stateCoordinates s d = rho

/-- PDF pp.1--3: n i.i.d. copies, grouped only within each party. -/
def groupedStateCopies {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d)) (n : ℕ) :
    Op (AssistanceBasis (fun i => d i ^ n)) :=
  fun x y => ∏ j : Fin n, rho
    (fun i => (Dependency50.P42.copyIndex (d i) n).symm (x i) j)
    (fun i => (Dependency50.P42.copyIndex (d i) n).symm (y i) j)

/-- PDF pp.2,7: partial trace onto a specified group of distinct parties. -/
def partyMarginal {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d)) (s : Finset (Fin m)) :=
  Claimed50.P33.forgetEnvironment
    (Claimed50.P33.registerMarginal (Claimed50.P33.trivialExtension rho) s)

/-- PDF pp.1--2: entropy of the actual reduced state. -/
def partyEntropy {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d)) (s : Finset (Fin m)) : ℝ :=
  vnEntropy (partyMarginal rho s)

/-- PDF pp.2--3: ordered two-party marginal; all other factors are traced out. -/
def pairMarginal {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d)) (a b : Fin m) :
    Op (Fin (d a) × Fin (d b)) :=
  fun u v => ∑ x : AssistanceBasis d, ∑ y : AssistanceBasis d,
    if x a = u.1 ∧ y a = v.1 ∧ x b = u.2 ∧ y b = v.2 ∧
      (∀ i, i ≠ a → i ≠ b → x i = y i) then rho x y else 0

/-- PDF pp.2,7: all cuts separating a from b, including both extreme cuts.
The finite index set is nonempty even when there are no helpers. -/
def cutMinimum {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d)) (a b : Fin m) : ℝ :=
  (Finset.univ : Finset (Finset (Fin m))).inf' Finset.univ_nonempty
    (fun s => partyEntropy rho (insert a (s.erase b)))

/-- PDF pp.1,7: the accepted local Kraus-instrument relation with its acting
party exposed. This is precisely P33.LocalInstrument with that witness fixed;
its lifted Kraus operators act as the identity at every other party. -/
def InstrumentAt {m k : ℕ} (s : SState m) (p : Fin k → ℝ)
    (r : Fin k → SState m) (party : Fin m) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
  ∃ count : Fin k → ℕ,
  ∃ A : (j : Fin k) → Fin (count j) →
    Matrix (Fin ((r j).dims party)) (Fin (s.dims party)) ℂ,
  (∀ j i, i ≠ party → (r j).dims i = s.dims i) ∧
  (∑ j, ∑ z, (Claimed50.P33.liftLocalKraus s (r j) party (A j z))ᴴ *
    Claimed50.P33.liftLocalKraus s (r j) party (A j z)) = 1 ∧
  ∀ j, (p j : ℂ) • (r j).rho = ∑ z,
    Claimed50.P33.liftLocalKraus s (r j) party (A j z) * s.rho *
      (Claimed50.P33.liftLocalKraus s (r j) party (A j z))ᴴ

/-- PDF pp.1,5--6: a local channel without an outgoing public outcome. -/
def ChannelAt {m : ℕ} (s t : SState m) (party : Fin m) : Prop :=
  InstrumentAt s (fun _ : Fin 1 => 1) (fun _ => t) party

/-- PDF p.1: unconditional output, retaining every branch's probability. -/
def MixesTo {m : ℕ} (out : List (ℝ × SState m)) (t : SState m) : Prop :=
  (∀ w ∈ out, w.2.dims = t.dims) ∧ ∀ x y,
    Claimed50.P33.stateEntry t x y =
      (out.map fun w => (w.1 : ℂ) * Claimed50.P33.stateEntry w.2 x y).sum

/-- PDF pp.1,7: finite adaptive LOCC with only parties in allowed acting.
Every local instrument is complete; there are no quantum messages or supplied
entangled ancillas. Classical outcomes may select any later local instrument. -/
inductive RestrictedLocalTree {m : ℕ} (allowed : Finset (Fin m)) :
    SState m → List (ℝ × SState m) → Prop where
  | stop (s) : RestrictedLocalTree allowed s [(1,s)]
  | step (s) (k : ℕ) (p : Fin k → ℝ) (r : Fin k → SState m)
      (party : Fin m) (hp : party ∈ allowed) (hi : InstrumentAt s p r party)
      (next : Fin k → List (ℝ × SState m))
      (hn : ∀ j, RestrictedLocalTree allowed (r j) (next j)) :
      RestrictedLocalTree allowed s ((List.finRange k).flatMap fun j =>
        (next j).map fun w => (p j * w.1,w.2))

/-- PDF pp.2,7--8: each remaining helper has exactly one measurement turn,
then discards its quantum system and broadcasts its outcome. Later helpers
may depend on earlier messages. A and B may finally use ordinary two-way LOCC. -/
inductive HelperTree {m : ℕ} (a b : Fin m) : Finset (Fin m) →
    SState m → List (ℝ × SState m) → Prop where
  | finish (s) (out) (h : RestrictedLocalTree {a,b} s out) : HelperTree a b ∅ s out
  | step (remaining) (s) (k : ℕ) (p : Fin k → ℝ) (r : Fin k → SState m)
      (party : Fin m) (hp : party ∈ remaining) (hi : InstrumentAt s p r party)
      (hd : ∀ j, (r j).dims party = 1)
      (next : Fin k → List (ℝ × SState m))
      (hn : ∀ j, HelperTree a b (remaining.erase party) (r j) (next j)) :
      HelperTree a b remaining s ((List.finRange k).flatMap fun j =>
        (next j).map fun w => (p j * w.1,w.2))

/-- PDF pp.2,5--6: one helper instrument, one broadcast, then two local
message-dependent channels. The helper keeps its quantum output; local helper
postprocessing is absorbed into its instrument. No feedback or A--B messages. -/
def HelperBroadcast {m : ℕ} (a b c : Fin m) (s t : SState m) : Prop :=
  ∃ k : ℕ, ∃ p : Fin k → ℝ, ∃ r v w : Fin k → SState m,
    InstrumentAt s p r c ∧
    (∀ j, ChannelAt (r j) (v j) a) ∧ (∀ j, ChannelAt (v j) (w j) b) ∧
    MixesTo ((List.finRange k).map fun j => (p j,w j)) t

/-- PDF pp.1--2,5--7: the three distinct protocol classes. -/
inductive AssistanceProtocol where
  | locc
  | singleTurn
  | broadcast (helper : ℕ)

/-- PDF pp.1--2,5--7: physical conversion, without postselection. -/
def AssistanceConverts {m : ℕ} (kind : AssistanceProtocol) (a b : Fin m) (s t : SState m) : Prop :=
  match kind with
  | .locc => Claimed50.P33.LOCC s [(1,t)]
  | .singleTurn => ∃ out, HelperTree a b ((Finset.univ.erase a).erase b) s out ∧
      MixesTo out t
  | .broadcast c => ∃ hc : c < m, HelperBroadcast a b ⟨c,hc⟩ s t

/-- PDF pp.1--2: g shared cat bits and e Bell bits on edge a--b. At zero
counts every local output has dimension one. In applications g>0 only for m=3. -/
def targetDims {m : ℕ} (a b : Fin m) (g e : ℕ) : Fin m → ℕ :=
  fun i => if i = a ∨ i = b then 2 ^ (g+e) else 2 ^ g

/-- PDF pp.1--2: the exact joint GHZ^g tensor Bell^e ket, locally regrouped.
The coefficient and the shared labels fix relative signs and normalization. -/
def bellGhzTarget {m : ℕ} (a b : Fin m) (g e : ℕ) :
    EuclideanSpace ℂ (AssistanceBasis (targetDims a b g e)) :=
  WithLp.toLp 2 fun x => (Real.sqrt ((2 : ℝ) ^ (g+e)) : ℂ)⁻¹ *
    ∑ u : Fin (2 ^ g), ∑ v : Fin (2 ^ e),
      if ∀ i, (x i).val = if i = a ∨ i = b
        then u.val * 2 ^ e + v.val else u.val then 1 else 0

/-- PDF pp.1--2: a finite-block code with one joint target fidelity test.
Input is exactly n i.i.d. copies; all other quantum outputs are disposed of. -/
def DistillationBlock {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d))
    (kind : AssistanceProtocol) (a b : Fin m) (n g e : ℕ) (epsilon : ℝ) : Prop :=
  ∃ s t : SState m, RepresentsState s (fun i => d i ^ n) (groupedStateCopies rho n) ∧
    t.dims = targetDims a b g e ∧ AssistanceConverts kind a b s t ∧
    1 - epsilon ≤ rootFidelity (stateCoordinates t (targetDims a b g e))
      (pureDensity (bellGhzTarget a b g e))

/-- PDF pp.1--2: eventual positive-blocklength rate closure. Real rates are
nonnegative; integer output counts may be zero. Epsilon controls joint fidelity
and delta controls both rates. Algorithms are chosen before any measurement
outcome. No input-dependent extra resource is supplied. -/
def AssistedYield {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d))
    (kind : AssistanceProtocol) (a b : Fin m) (ghzRate eprRate : ℝ) : Prop :=
  0 ≤ ghzRate ∧ 0 ≤ eprRate ∧
  ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, N < n →
    ∃ g e : ℕ, (ghzRate - delta) * n ≤ g ∧ (eprRate - delta) * n ≤ e ∧
      DistillationBlock rho kind a b n g e epsilon

/-- PDF p.3: ensemble average entanglement across the displayed bipartition. -/
def averageEntanglement {A B : Type} [Fintype A] [Fintype B]
    (e : PureEnsemble (A × B)) : ℝ :=
  ∑ j, e.prob j * vnEntropy (traceRight (pureDensity (e.vector j)))

/-- PDF p.3: one-copy assistance, optimized over all finite normalized pure
ensembles. On density inputs the set is nonempty and bounded in
[0,min(log2 d_A,log2 d_B)]; invalid-input defaults are never used. -/
def assistance {A B : Type} [Fintype A] [Fintype B] (rho : Op (A × B)) : ℝ :=
  sSup {r | ∃ e : PureEnsemble (A × B), Information100.P08.pureAverage e = rho ∧
    r = averageEntanglement e}

/-- PDF p.3: a fixed local basis identification for the purifying register. -/
def purificationPairEquiv (a b : ℕ) : (Fin a × Fin b) ≃ Fin (a*b) :=
  Fintype.equivFinOfCardEq (by simp)

/-- PDF pp.2--3: C holds the canonical purification of the given AB density;
it is not an independently chosen resource. All purifications give the same
operational rate up to a local isometry on C. -/
def tripartitePurification {a b : ℕ} (rho : Op (Fin a × Fin b)) :
    EuclideanSpace ℂ (AssistanceBasis (![a,b,a*b] : Fin 3 → ℕ)) :=
  WithLp.toLp 2 fun x => Information100.P08.canonicalPurification rho
    ((purificationPairEquiv a b).symm (x 2), (x 0,x 1))

/-- PDF p.3: operational EPR yield of the purification, defined independently
of the ensemble roof and its regularization. The rate set contains zero and
is bounded for every physical finite-dimensional state. -/
def operationalAssistance {a b : ℕ} (rho : Op (Fin a × Fin b)) : ℝ :=
  sSup {r | AssistedYield (pureDensity (tripartitePurification rho)) .locc 0 1 0 r}

/-- PDF p.3: n indexes n+1 copies, never a division by zero. -/
def assistanceSequence {a b : ℕ} (rho : Op (Fin a × Fin b)) (n : ℕ) : ℝ :=
  assistance (Dependency50.P42.dimensionedPower rho (n+1)) / (n+1 : ℕ)

/-- Sanity: the zero-copy matrix has every scalar entry equal to one. -/
example {m : ℕ} {d : Fin m → ℕ} (rho : Op (AssistanceBasis d))
    (x y : AssistanceBasis (fun i => d i ^ 0)) : groupedStateCopies rho 0 x y = 1 := by
  simp [groupedStateCopies]

/-- Sanity: two distinct receivers leave no helpers in the two-party case. -/
example : ((Finset.univ : Finset (Fin 2)).erase 0).erase 1 = ∅ := by decide

/-- Sanity: zero output resources use only one-dimensional local registers. -/
example {m : ℕ} (a b i : Fin m) : targetDims a b 0 0 i = 1 := by
  simp [targetDims]

/-- PDF p.3, Example 4: the six signed determinant-state amplitudes. -/
def determinantVector : EuclideanSpace ℂ (AssistanceBasis (fun _ : Fin 3 => 3)) :=
  WithLp.toLp 2 fun x => (Real.sqrt 6 : ℂ)⁻¹ *
    ((if (x 0,x 1,x 2) = (0,1,2) then 1 else 0) +
     (if (x 0,x 1,x 2) = (1,2,0) then 1 else 0) +
     (if (x 0,x 1,x 2) = (2,0,1) then 1 else 0) -
     (if (x 0,x 1,x 2) = (2,1,0) then 1 else 0) -
     (if (x 0,x 1,x 2) = (1,0,2) then 1 else 0) -
     (if (x 0,x 1,x 2) = (0,2,1) then 1 else 0))

/-- PDF p.3, Example 4: the actual two-qutrit reduction. -/
def determinantMarginal : Op (Fin 3 × Fin 3) :=
  pairMarginal (pureDensity determinantVector) 0 1

/-- PDF p.3, Example 4: an unnormalized antisymmetric two-qutrit ket. -/
def antisymmetricPairAmplitude (i j : Fin 3) (x : Fin 3 × Fin 3) : ℂ :=
  (if x = (i,j) then 1 else 0) - (if x = (j,i) then 1 else 0)

/-- PDF p.3, Example 4: PLUS of two orthogonal tensor products, coefficient
1/sqrt(8); grouped as A1A2:B1B2. -/
def superadditiveWitness : EuclideanSpace ℂ ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)) :=
  WithLp.toLp 2 fun x => (Real.sqrt 8 : ℂ)⁻¹ *
    (antisymmetricPairAmplitude 0 1 (x.1.1,x.2.1) * antisymmetricPairAmplitude 0 1 (x.1.2,x.2.2) +
     antisymmetricPairAmplitude 1 2 (x.1.1,x.2.1) * antisymmetricPairAmplitude 1 2 (x.1.2,x.2.2))

/-- PDF p.3, Example 4: the orbit preserves each copy's antisymmetric subspace. -/
def witnessOrbit (U V : Matrix.unitaryGroup (Fin 3) ℂ) :=
  act (Matrix.kronecker (Matrix.kronecker (U : Op (Fin 3)) (V : Op (Fin 3)))
    (Matrix.kronecker (U : Op (Fin 3)) (V : Op (Fin 3)))) superadditiveWitness

/-- Sanity: the positive 01 tensor 01 amplitude has the printed coefficient. -/
example : superadditiveWitness ((0,0),(1,1)) = (Real.sqrt 8 : ℂ)⁻¹ := by
  simp [superadditiveWitness, antisymmetricPairAmplitude]

/-- PDF p.6, Example 10: alpha|0>Phi+ + beta|1>Phi-, with positive Bell phase
on |00> and opposite phases on |11>. Parameters are real as in the source. -/
def upsilonVector (alpha beta : ℝ) : EuclideanSpace ℂ (AssistanceBasis (fun _ : Fin 3 => 2)) :=
  WithLp.toLp 2 fun x => (Real.sqrt 2 : ℂ)⁻¹ *
    (if x 1 = x 2 then
      if x 0 = 0 then (alpha : ℂ) else if x 1 = 0 then (beta : ℂ) else -(beta : ℂ)
    else 0)

/-- PDF pp.6--7, Example 11: normalized W ket. -/
def symmetricWKet : EuclideanSpace ℂ (AssistanceBasis (fun _ : Fin 3 => 2)) :=
  WithLp.toLp 2 fun x => if (x 0).val + (x 1).val + (x 2).val = 1
    then (Real.sqrt 3 : ℂ)⁻¹ else 0

/-- PDF p.8, Section VII: normalized maximally entangled input, trace one. -/
def choiKet (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun x => if x.1 = x.2 then (Real.sqrt (d : ℝ) : ℂ)⁻¹ else 0

/-- PDF pp.4--5: the memoryless isometric channel to Bob and the helper's
environment, with each party's n systems regrouped locally. -/
def dimensionedDilationPower {a b c : ℕ} (U : Matrix (Fin b × Fin c) (Fin a) ℂ) (n : ℕ) :
    Matrix (Fin (b^n) × Fin (c^n)) (Fin (a^n)) ℂ :=
  fun x y => Information100.P67.dilationPower U n
    ((Dependency50.P42.copyIndex b n).symm x.1,
     (Dependency50.P42.copyIndex c n).symm x.2)
    ((Dependency50.P42.copyIndex a n).symm y)

/-- PDF p.5: after encoding one half of a Bell test state, apply U^tensor n
only to the transmitted register. Parties are Alice's memory, Bob, Charlie,
and an UNTOUCHED external reference, in that order. The initial reference
entanglement is local to the sender's test input, not a supplied A--B resource. -/
def transmissionState {a b c : ℕ} (U : Matrix (Fin b × Fin c) (Fin a) ℂ)
    (n k memory : ℕ) (Enc : Superop (Fin (2^k)) (Fin memory × Fin (a^n))) :
    Op (AssistanceBasis (![memory,b^n,c^n,2^k] : Fin 4 → ℕ)) :=
  let encoded := idTensorSuperop Enc (pureDensity (choiKet (2^k)))
  let V := dimensionedDilationPower U n
  fun x y => ∑ u : Fin (a^n), ∑ v : Fin (a^n),
    encoded (x 3,(x 0,u)) (y 3,(y 0,v)) *
      V (x 1,x 2) u * conj (V (y 1,y 2) v)

/-- PDF pp.4--5, Theorem 8: an actual n-use transmission code. The reference
(party 3) is excluded from every local operation. With unlimited=false there
is only C's instrument and one broadcast followed by Alice/Bob local channels;
with unlimited=true all three honest parties may use adaptive LOCC. Arbitrary
local encoder memory is allowed and all work is discarded in the final Bell
test. No preshared honest-party entanglement or quantum side message occurs. -/
def TransmissionBlock {a b c : ℕ} (U : Matrix (Fin b × Fin c) (Fin a) ℂ)
    (unlimited : Bool) (n k : ℕ) (epsilon : ℝ) : Prop :=
  ∃ memory : ℕ, 0 < memory ∧
    ∃ Enc : Superop (Fin (2^k)) (Fin memory × Fin (a^n)), IsChannel Enc ∧
    ∃ s t : SState 4,
      RepresentsState s (![memory,b^n,c^n,2^k]) (transmissionState U n k memory Enc) ∧
      t.dims = targetDims (3 : Fin 4) 1 0 k ∧
      (if unlimited then ∃ out, RestrictedLocalTree {0,1,2} s out ∧ MixesTo out t
       else HelperBroadcast 0 1 2 s t) ∧
      1-epsilon ≤ rootFidelity (stateCoordinates t (targetDims (3 : Fin 4) 1 0 k))
        (pureDensity (bellGhzTarget (3 : Fin 4) 1 0 k))

/-- PDF pp.4--5: environment-assisted quantum communication rates, evaluated
on the full purifying-reference Bell test, for all sufficiently large positive n. -/
def TransmissionRate {a b c : ℕ} (U : Matrix (Fin b × Fin c) (Fin a) ℂ)
    (unlimited : Bool) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N < n → ∃ k : ℕ, (r-delta)*n ≤ k ∧
      TransmissionBlock U unlimited n k epsilon

/-- PDF p.5, Theorem 8: optimization over normalized input density matrices.
The value set is nonempty and bounded on positive-dimensional channels. -/
def assistedCapacityObjective {a b : ℕ} (T : Superop (Fin a) (Fin b)) : ℝ :=
  sSup {r | ∃ rho : Op (Fin a), IsDensityMatrix rho ∧
    r = min (vnEntropy rho) (vnEntropy (T rho))}

/-- Sanity: the reference labels in transmissionState are never summed over. -/
example {a b c : ℕ} (U : Matrix (Fin b × Fin c) (Fin a) ℂ)
    (n k memory : ℕ) (Enc : Superop (Fin (2^k)) (Fin memory × Fin (a^n)))
    (x y : AssistanceBasis (![memory,b^n,c^n,2^k] : Fin 4 → ℕ)) :
    transmissionState U n k memory Enc x y =
      ∑ u : Fin (a^n), ∑ v : Fin (a^n),
        (idTensorSuperop Enc (pureDensity (choiKet (2^k))))
          (x 3,(x 0,u)) (y 3,(y 0,v)) *
        dimensionedDilationPower U n (x 1,x 2) u * conj (dimensionedDilationPower U n (y 1,y 2) v) := by
  rfl

/-- PDF p.6, proof of Theorem 9: a one-way-broadcast common-randomness code.
X is the ENTIRE public message. C also keeps a private k-bit output, while
A and B use X-dependent local POVMs with private outputs. All branches are
included. This POVM form includes arbitrary local ancillary randomness and
private postprocessing. No private outcome is silently made public. -/
structure RandomnessCode (d : Fin 3 → ℕ) (k : ℕ) where
  messages : ℕ
  cEffect : (Fin messages × Fin (2^k)) → Op (Fin (d 2))
  aEffect : Fin messages → Fin (2^k) → Op (Fin (d 0))
  bEffect : Fin messages → Fin (2^k) → Op (Fin (d 1))
  cPovm : IsPOVM cEffect
  aPovm : ∀ x, IsPOVM (aEffect x)
  bPovm : ∀ x, IsPOVM (bEffect x)

/-- PDF p.6: joint law of the public message and all three private strings,
computed from the product local effects on the actual shared state. -/
def randomnessLaw {d : Fin 3 → ℕ} {k : ℕ} (rho : Op (AssistanceBasis d))
    (code : RandomnessCode d k) (x : Fin code.messages) (u v w : Fin (2^k)) : ℝ :=
  effectProb (fun a b => code.aEffect x u (a 0) (b 0) *
    code.bEffect x v (a 1) (b 1) * code.cEffect (x,w) (a 2) (b 2)) rho

/-- PDF p.6: total variation from Uniform(identical k-bit strings) times
law(X). Keeping X is essential: broadcasting fresh random bits alone fails. -/
def randomnessError {d : Fin 3 → ℕ} {k : ℕ} (rho : Op (AssistanceBasis d))
    (code : RandomnessCode d k) : ℝ :=
  (1/2 : ℝ) * ∑ x, ∑ u, ∑ v, ∑ w,
    |randomnessLaw rho code x u v w -
      (if u = v ∧ v = w then (2 : ℝ)^(- (k : ℤ)) else 0) *
        (∑ u2, ∑ v2, ∑ w2, randomnessLaw rho code x u2 v2 w2)|

/-- PDF p.6: independent shared randomness at an eventual i.i.d. rate;
the total-variation error tests uniformity, agreement, AND transcript independence. -/
def RandomnessRate {d : Fin 3 → ℕ} (rho : Op (AssistanceBasis d)) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ epsilon > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
    ∀ n : ℕ, N < n → ∃ k : ℕ, (r-delta)*n ≤ k ∧
      ∃ code : RandomnessCode (fun i => d i ^ n) k,
        randomnessError (groupedStateCopies rho n) code ≤ epsilon

/-- PDF p.9: a nearby pure-state ensemble, every component having entropy
at least n(rate-delta). Approximation is in trace norm, not channel norm and
not a componentwise fidelity to maximally entangled vectors. -/
def HighEntropyEnsemble {a b : ℕ} (rho : Op (Fin a × Fin b))
    (n : ℕ) (rate epsilon delta : ℝ) : Prop :=
  ∃ ens : PureEnsemble (Fin (a^n) × Fin (b^n)),
    traceNorm (Information100.P08.pureAverage ens -
      Dependency50.P42.dimensionedPower rho n) ≤ epsilon ∧
    ∀ j, (n : ℝ)*(rate-delta) ≤
      vnEntropy (traceRight (pureDensity (ens.vector j)))

/-- PDF p.9: local typical-subspace consequence, expressed by actual local
isometric embeddings. The compressed state is the normalized local projection
of rho^tensor n; the positive projection weight prevents division by zero.
Both the discarded-subspace error and the ensemble error are retained.
Logarithmic local dimensions approximate n times the respective marginal
entropies. These are subspace isometries, never full-input channel isometries. -/
def TypicalHighEntropyEnsemble {a b : ℕ} (rho : Op (Fin a × Fin b))
    (n : ℕ) (epsilon delta : ℝ) : Prop :=
  ∃ da db : ℕ, 0 < da ∧ 0 < db ∧
    ∃ VA : Matrix (Fin (a^n)) (Fin da) ℂ,
    ∃ VB : Matrix (Fin (b^n)) (Fin db) ℂ,
      VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧
      |Real.logb 2 da - (n : ℝ)*vnEntropy (traceRight rho)| ≤ n*delta ∧
      |Real.logb 2 db - (n : ℝ)*vnEntropy (traceLeft rho)| ≤ n*delta ∧
      let V := Matrix.kronecker VA VB
      let projected := Vᴴ * Dependency50.P42.dimensionedPower rho n * V
      let weight := projected.trace.re
      0 < weight ∧
      let sigma := (weight : ℂ)⁻¹ • projected
      IsDensityMatrix sigma ∧
      traceNorm (Dependency50.P42.dimensionedPower rho n - V * sigma * Vᴴ) ≤ epsilon ∧
      ∃ ens : PureEnsemble (Fin da × Fin db),
        traceNorm (Information100.P08.pureAverage ens - sigma) ≤ epsilon ∧
        ∀ j, (n : ℝ)*(min (vnEntropy (traceRight rho)) (vnEntropy (traceLeft rho)) - delta) ≤
          vnEntropy (traceRight (pureDensity (ens.vector j)))

end

end QAlgorithms.Papers.Independent.Intake100.P93


