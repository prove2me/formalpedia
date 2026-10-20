-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06
-- name    : QAlgorithms_Papers_Independent_Frontier30_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T18:23:19.472361+00:00
-- url     : https://prove2.me/theorems/3bdfa196-1589-4d78-a8a5-81c93638f7c9
-- title:
--   Definitions for On Feedback and the Classical Capacity of a Noisy Quantum Channel
-- statement:
--   The objects the formalized statements of *On Feedback and the Classical Capacity of a Noisy Quantum Channel* (arXiv:quant-ph/0305176) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ChannelValid`: PDF pp.1-2: positive finite ports and a completely positive trace-preserving map.
--   - `forwardTensorBlock`: PDF p.2, (6): k independent uses, including entangled inputs within the block. The frozen P71.channelPower supplies the tensor map; this adapter only packages its finite function basis into the rectangular channel record using equivFin.
--   - `Prior`: PDF p.2, (2): arbitrary prior, allowing zero-probability messages.
--   - `uniformPrior`: PDF pp.1-2: the uniform prior used for operational average decoding error.
--   - `FeedbackExecution`: PDF pp.2-3, (7)-(10): a finite executed protocol, with changing local memories. Alice's initial state depends on the message; Bob's seed does not. Every encoder and response is selected before the message. A response may store the classical outcome in Alice's memory. Bob's memory includes all systems he retains, including any retained classical records. Branch Kraus families implement his instruments. The message reference is external and none of these maps acts on it. This differs from frozen P07.Protocol, which distills a key from a supplied bipartite state using one-way classical messages rather than noisy channel calls.
--   - `FeedbackExecution.Valid`: PDF pp.2-3: legality contains only physical normalization and access conditions. The branch sum is TP; each branch is CP by its actual Kraus body. No information inequality, separability restriction, or success bound is part of legality.
--   - `FeedbackExecution.prepare`: PDF pp.2-3: Alice prepares the next input, leaving every Bob block untouched.
--   - `FeedbackExecution.transmit`: PDF p.3, (9): the actual channel call, identity on both retained memories, including their off-diagonal blocks. Output is ordered Alice,(Bob,channel output).
--   - `FeedbackExecution.feedbackBranch`: PDF p.3, (10): one actual classical feedback branch; the outcome is copied classically, so there is no coherent sum of branch amplitudes or quantum feedback.
--   - `FeedbackExecution.update`: PDF p.3, (10): average LOCC update after the specified channel call.
--   - `FeedbackExecution.state`: PDF pp.2-3, (7)-(12): derived conditional states, not independently supplied data. Initialization is a product, with no prior shared entanglement or correlated seed.
--   - `FeedbackExecution.branchState`: PDF p.3: unnormalized execution conditional on the complete feedback transcript. An impossible transcript is zero, without division by its probability.
--   - `FeedbackExecution.History`: PDF p.3: a complete finite classical feedback transcript through j calls.
--   - `FeedbackExecution.historySequence`: PDF p.3: extend a finite transcript by dummy values at unused positions. Only its first j entries enter branchState at time j.
--   - `FeedbackExecution.recordedState`: PDF p.3, discussion following (15): automatically retain EVERY measurement outcome as a classical record. Off-diagonal transcript blocks are zero. These records are present even if the quantum-memory Kraus map forgets them.
--   - `FeedbackExecution.recordedSent`: PDF pp.3-4: actual pre-feedback state retaining all earlier classical records, with the new channel output adjoined to Bob's memory.
--   - `cutState`: PDF p.4, (22)-(23): average total state, with the untouched orthogonal message reference grouped with Bob. The other side is all retained sender memory. Message-dependent separable decompositions are allowed.
--   - `FeedbackExecution.SeparableCuts`: PDF p.4, III.B: separability at each feedback cut between blocks. There is no cut inside a block; its channel inputs may be entangled.
--   - `FeedbackExecution.receiver`: PDF pp.2-3: every register retained by Bob, prior to the final decoder.
--   - `FeedbackExecution.information`: PDF p.2, (4): I(M:B_final) for the actual cq ensemble, in bits. Orthogonal classical message flags make this exactly the quantum mutual information.
--   - `FeedbackExecution.accessible`: PDF p.3, (20): accessible information of this SAME executed protocol and prior. Only the final POVM is optimized; the channel uses and ensemble remain fixed. For legal normalized data, the nonempty value set is bounded by message entropy.
--   - `FeedbackExecution.splitReceived`: PDF p.4, (24): the actual state on (M,B_previous),new_output after call j. Alice alone is traced out; no unrelated ensemble or marginal is substituted.
--   - `bipartiteInformation`: PDF p.4, (24), corrected: S(X)+S(Y)-S(XY), including the WHOLE first system. Printed S(M) is changed to S(M Q1prime), as required by the displayed left side.
--   - `BlockCode`: PDF p.2, III.A: block lengths count physical calls of the same memoryless N.
--   - `BlockCode.Valid`: PDF pp.1-3: positive code length and message count, with legal executed maps.
--   - `BlockCode.uses`: PDF p.2, III.A: the actual total number of forward uses, not the number of cuts.
--   - `BlockCode.error`: PDF pp.1-2: uniform-message average error from the executed final POVM.
--   - `BlockCode.rate`: PDF p.2, (6): communication rate in bits per physical forward use.
--   - `Achieves`: PDF pp.1-2: an operational code sequence at rate R. No entropy enters validity, error, rate, or achievability. The eventual lower bound avoids a real liminf's junk value on unbounded rate sequences. The restriction selects a resource class.
--   - `operationalCapacity`: PDF pp.1-2: nonnegative extended supremum of operationally achievable rates. The empty set has capacity zero. Positive-dimensional channels admit zero-rate one-message codes; no finite-dimensional entropy supremum defines this capacity.
--   - `unassistedCapacity`: PDF pp.1-2, (6): one arbitrarily large entangled block and no intervening feedback. Any final local instrument is absorbed in the decoder. This is operational C.
--   - `separableFeedbackCapacity`: PDF p.4, III.B: arbitrarily large blocks with separable inter-block feedback cuts.
-- source:
--   On Feedback and the Classical Capacity of a Noisy Quantum Channel, arXiv:quant-ph/0305176v1, https://arxiv.org/abs/quant-ph/0305176v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

/-! Bowen and Nagarajan, arXiv:quant-ph/0305176v1, PDF pp.1-4.
The accepted rectangular channel record is reused regardless of its historical
name `Backward`. Here its map is always a FORWARD channel. All local definitions
are finite dimensional. Capacity is operational, with uniform-message average
error, in bits per physical forward use; it is not defined through entropy.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology
open Filter

namespace QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)
open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF pp.1-2: positive finite ports and a completely positive trace-preserving map. -/
def ChannelValid (N : Backward) : Prop :=
  0 < N.input ∧ 0 < N.output ∧ IsChannel N.map

/-- PDF p.2, (6): k independent uses, including entangled inputs within the block.
The frozen P71.channelPower supplies the tensor map; this adapter only packages
its finite function basis into the rectangular channel record using equivFin. -/
def forwardTensorBlock (N : Backward) (k : ℕ) : Backward where
  input := Fintype.card (Fin k → Fin N.input)
  output := Fintype.card (Fin k → Fin N.output)
  map := fun X u v =>
    QAlgorithms.Papers.Independent.Information100.P71.channelPower N.map k
      (fun x y => X (Fintype.equivFin _ x) (Fintype.equivFin _ y))
      ((Fintype.equivFin _).symm u) ((Fintype.equivFin _).symm v)

/-- PDF p.2, (2): arbitrary prior, allowing zero-probability messages. -/
def Prior {M : ℕ} (p : Fin M → ℝ) : Prop :=
  (∀ m, 0 ≤ p m) ∧ ∑ m, p m = 1

/-- PDF pp.1-2: the uniform prior used for operational average decoding error. -/
def uniformPrior (M : ℕ) : Fin M → ℝ := fun _ => (M : ℝ)⁻¹

/-- PDF pp.2-3, (7)-(10): a finite executed protocol, with changing local memories.
Alice's initial state depends on the message; Bob's seed does not. Every encoder
and response is selected before the message. A response may store the classical
outcome in Alice's memory. Bob's memory includes all systems he retains, including
any retained classical records. Branch Kraus families implement his instruments.
The message reference is external and none of these maps acts on it.
This differs from frozen P07.Protocol, which distills a key from a supplied
bipartite state using one-way classical messages rather than noisy channel calls. -/
structure FeedbackExecution (channels : ℕ → Backward) (n M : ℕ) where
  aliceDim : ℕ → ℕ
  bobDim : ℕ → ℕ
  aliceInitial : Fin M → Matrix (Fin (aliceDim 0)) (Fin (aliceDim 0)) ℂ
  bobInitial : Matrix (Fin (bobDim 0)) (Fin (bobDim 0)) ℂ
  encode : (j : ℕ) → Superop (Fin (aliceDim j))
    (Fin (aliceDim (j+1)) × Fin (channels j).input)
  outcomes : ℕ → ℕ
  rank : ℕ → ℕ
  bobKraus : (j : ℕ) → Fin (outcomes j) → Fin (rank j) →
    Matrix (Fin (bobDim (j+1))) (Fin (bobDim j) × Fin (channels j).output) ℂ
  respond : (j : ℕ) → Fin (outcomes j) →
    Superop (Fin (aliceDim (j+1))) (Fin (aliceDim (j+1)))
  decoder : Fin M → Matrix
    (((j : Fin n) → Fin (outcomes j.val)) × Fin (bobDim n))
    (((j : Fin n) → Fin (outcomes j.val)) × Fin (bobDim n)) ℂ

/-- PDF pp.2-3: legality contains only physical normalization and access conditions.
The branch sum is TP; each branch is CP by its actual Kraus body. No information
inequality, separability restriction, or success bound is part of legality. -/
def FeedbackExecution.Valid {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M) : Prop :=
  0 < M ∧ (∀ j ≤ n, 0 < P.aliceDim j ∧ 0 < P.bobDim j) ∧
  (∀ m, IsDensityMatrix (P.aliceInitial m)) ∧ IsDensityMatrix P.bobInitial ∧
  IsPOVM P.decoder ∧ ∀ j < n,
    ChannelValid (ch j) ∧ IsChannel (P.encode j) ∧ 0 < P.outcomes j ∧
    (∑ x, ∑ k, (P.bobKraus j x k)ᴴ * P.bobKraus j x k = 1) ∧
    ∀ x, IsChannel (P.respond j x)

/-- PDF pp.2-3: Alice prepares the next input, leaving every Bob block untouched. -/
def FeedbackExecution.prepare {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (j : ℕ) (X : Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ) :
    Matrix ((Fin (P.aliceDim (j+1)) × Fin (ch j).input) × Fin (P.bobDim j))
      ((Fin (P.aliceDim (j+1)) × Fin (ch j).input) × Fin (P.bobDim j)) ℂ :=
  tensorAction (P.encode j) id X

/-- PDF p.3, (9): the actual channel call, identity on both retained memories,
including their off-diagonal blocks. Output is ordered Alice,(Bob,channel output). -/
def FeedbackExecution.transmit {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (j : ℕ) (X : Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ) :
    Matrix (Fin (P.aliceDim (j+1)) × (Fin (P.bobDim j) × Fin (ch j).output))
      (Fin (P.aliceDim (j+1)) × (Fin (P.bobDim j) × Fin (ch j).output)) ℂ :=
  fun u v => (ch j).map
    (fun a b => P.prepare j X ((u.1,a),u.2.1) ((v.1,b),v.2.1)) u.2.2 v.2.2

/-- PDF p.3, (10): one actual classical feedback branch; the outcome is copied
classically, so there is no coherent sum of branch amplitudes or quantum feedback. -/
def FeedbackExecution.feedbackBranch {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (j : ℕ) (x : Fin (P.outcomes j)) :
    Superop (Fin (P.aliceDim (j+1)) × (Fin (P.bobDim j) × Fin (ch j).output))
      (Fin (P.aliceDim (j+1)) × Fin (P.bobDim (j+1))) :=
  tensorAction (P.respond j x) (krausApply (P.bobKraus j x))

/-- PDF p.3, (10): average LOCC update after the specified channel call. -/
def FeedbackExecution.update {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (j : ℕ) (X : Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ) :
    Matrix (Fin (P.aliceDim (j+1)) × Fin (P.bobDim (j+1)))
      (Fin (P.aliceDim (j+1)) × Fin (P.bobDim (j+1))) ℂ :=
  ∑ x, P.feedbackBranch j x (P.transmit j X)

/-- PDF pp.2-3, (7)-(12): derived conditional states, not independently supplied data.
Initialization is a product, with no prior shared entanglement or correlated seed. -/
def FeedbackExecution.state {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M) (m : Fin M) :
    (j : ℕ) → Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ
  | 0 => Matrix.kronecker (P.aliceInitial m) P.bobInitial
  | j+1 => P.update j (P.state m j)

/-- PDF p.3: unnormalized execution conditional on the complete feedback transcript.
An impossible transcript is zero, without division by its probability. -/
def FeedbackExecution.branchState {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (m : Fin M) (history : ℕ → ℕ) :
    (j : ℕ) → Matrix (Fin (P.aliceDim j) × Fin (P.bobDim j))
      (Fin (P.aliceDim j) × Fin (P.bobDim j)) ℂ
  | 0 => Matrix.kronecker (P.aliceInitial m) P.bobInitial
  | j+1 => if h : history j < P.outcomes j then
      P.feedbackBranch j ⟨history j,h⟩ (P.transmit j (P.branchState m history j))
    else 0

/-- PDF p.3: a complete finite classical feedback transcript through j calls. -/
abbrev FeedbackExecution.History {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (j : ℕ) := (t : Fin j) → Fin (P.outcomes t.val)

/-- PDF p.3: extend a finite transcript by dummy values at unused positions.
Only its first j entries enter branchState at time j. -/
def FeedbackExecution.historySequence {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) {j : ℕ} (h : P.History j) : ℕ → ℕ :=
  fun t => if ht : t < j then (h ⟨t,ht⟩).val else 0

/-- PDF p.3, discussion following (15): automatically retain EVERY measurement
outcome as a classical record. Off-diagonal transcript blocks are zero.
These records are present even if the quantum-memory Kraus map forgets them. -/
def FeedbackExecution.recordedState {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (m : Fin M) (j : ℕ) :
    Matrix (Fin (P.aliceDim j) × (P.History j × Fin (P.bobDim j)))
      (Fin (P.aliceDim j) × (P.History j × Fin (P.bobDim j))) ℂ :=
  fun u v => if u.2.1 = v.2.1 then
    P.branchState m (P.historySequence u.2.1) j (u.1,u.2.2) (v.1,v.2.2) else 0

/-- PDF pp.3-4: actual pre-feedback state retaining all earlier classical records,
with the new channel output adjoined to Bob's memory. -/
def FeedbackExecution.recordedSent {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (m : Fin M) (j : ℕ) :
    Matrix (Fin (P.aliceDim (j+1)) ×
        (P.History j × (Fin (P.bobDim j) × Fin (ch j).output)))
      (Fin (P.aliceDim (j+1)) ×
        (P.History j × (Fin (P.bobDim j) × Fin (ch j).output))) ℂ :=
  fun u v => if u.2.1 = v.2.1 then
    P.transmit j (P.branchState m (P.historySequence u.2.1) j)
      (u.1,u.2.2) (v.1,v.2.2) else 0

/-- PDF p.4, (22)-(23): average total state, with the untouched orthogonal
message reference grouped with Bob. The other side is all retained sender memory.
Message-dependent separable decompositions are allowed. -/
def cutState {A B : Type} {M : ℕ} (p : Fin M → ℝ)
    (X : Fin M → Matrix (A × B) (A × B) ℂ) :
    Matrix ((Fin M × B) × A) ((Fin M × B) × A) ℂ :=
  fun u v => if u.1.1 = v.1.1 then (p u.1.1 : ℂ) *
    X u.1.1 (u.2,u.1.2) (v.2,v.1.2) else 0

/-- PDF p.4, III.B: separability at each feedback cut between blocks.
There is no cut inside a block; its channel inputs may be entangled. -/
def FeedbackExecution.SeparableCuts {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (p : Fin M → ℝ) : Prop :=
  ∀ j, j+1 < n →
    Entanglement.IsSeparablePositive
      (cutState p (fun m => P.recordedSent m j)) ∧
    Entanglement.IsSeparablePositive (cutState p (fun m => P.recordedState m (j+1)))

/-- PDF pp.2-3: every register retained by Bob, prior to the final decoder. -/
def FeedbackExecution.receiver {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (m : Fin M) : Matrix (P.History n × Fin (P.bobDim n))
      (P.History n × Fin (P.bobDim n)) ℂ :=
  traceLeft (P.recordedState m n)

/-- PDF p.2, (4): I(M:B_final) for the actual cq ensemble, in bits.
Orthogonal classical message flags make this exactly the quantum mutual information. -/
def FeedbackExecution.information {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (p : Fin M → ℝ) : ℝ :=
  vnEntropy (∑ m, (p m : ℂ) • P.receiver m) -
    ∑ m, p m * vnEntropy (P.receiver m)

/-- PDF p.3, (20): accessible information of this SAME executed protocol and prior.
Only the final POVM is optimized; the channel uses and ensemble remain fixed.
For legal normalized data, the nonempty value set is bounded by message entropy. -/
def FeedbackExecution.accessible {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (p : Fin M → ℝ) : ℝ :=
  sSup {r | ∃ k : ℕ, ∃ D : Fin k → Matrix (P.History n × Fin (P.bobDim n))
      (P.History n × Fin (P.bobDim n)) ℂ,
    IsPOVM D ∧ r = mutualInfoBits (fun z : Fin M × Fin k =>
      p z.1 * effectProb (D z.2) (P.receiver z.1))}

/-- PDF p.4, (24): the actual state on (M,B_previous),new_output after call j.
Alice alone is traced out; no unrelated ensemble or marginal is substituted. -/
def FeedbackExecution.splitReceived {ch : ℕ → Backward} {n M : ℕ}
    (P : FeedbackExecution ch n M) (p : Fin M → ℝ) (j : ℕ) :
    Matrix ((Fin M × (P.History j × Fin (P.bobDim j))) × Fin (ch j).output)
      ((Fin M × (P.History j × Fin (P.bobDim j))) × Fin (ch j).output) ℂ :=
  fun u v => if u.1.1 = v.1.1 ∧ u.1.2.1 = v.1.2.1 then (p u.1.1 : ℂ) *
    ∑ a, P.transmit j
      (P.branchState u.1.1 (P.historySequence u.1.2.1) j)
      (a,(u.1.2.2,u.2)) (a,(v.1.2.2,v.2)) else 0

/-- PDF p.4, (24), corrected: S(X)+S(Y)-S(XY), including the WHOLE first system.
Printed S(M) is changed to S(M Q1prime), as required by the displayed left side. -/
def bipartiteInformation {A B : Type} [Fintype A] [Fintype B]
    (X : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (traceRight X) + vnEntropy (traceLeft X) - vnEntropy X

/-- PDF p.2, III.A: block lengths count physical calls of the same memoryless N. -/
structure BlockCode (N : Backward) where
  rounds : ℕ
  messages : ℕ
  width : ℕ → ℕ
  protocol : FeedbackExecution (fun j => forwardTensorBlock N (width j)) rounds messages

/-- PDF pp.1-3: positive code length and message count, with legal executed maps. -/
def BlockCode.Valid {N : Backward} (c : BlockCode N) : Prop :=
  0 < c.rounds ∧ (∀ j < c.rounds, 0 < c.width j) ∧ c.protocol.Valid

/-- PDF p.2, III.A: the actual total number of forward uses, not the number of cuts. -/
def BlockCode.uses {N : Backward} (c : BlockCode N) : ℕ :=
  ∑ j ∈ Finset.range c.rounds, c.width j

/-- PDF pp.1-2: uniform-message average error from the executed final POVM. -/
def BlockCode.error {N : Backward} (c : BlockCode N) : ℝ :=
  1 - ∑ m, uniformPrior c.messages m *
    effectProb (c.protocol.decoder m) (c.protocol.receiver m)

/-- PDF p.2, (6): communication rate in bits per physical forward use. -/
def BlockCode.rate {N : Backward} (c : BlockCode N) : ℝ :=
  Real.logb 2 c.messages / c.uses

/-- PDF pp.1-2: an operational code sequence at rate R. No entropy enters validity,
error, rate, or achievability. The eventual lower bound avoids a real liminf's
junk value on unbounded rate sequences. The restriction selects a resource class. -/
def Achieves {N : Backward} (restriction : BlockCode N → Prop)
    (codes : ℕ → BlockCode N) (R : ℝ) : Prop :=
  0 ≤ R ∧ (∀ k, (codes k).Valid ∧ restriction (codes k)) ∧
  Tendsto (fun k => (codes k).uses) atTop atTop ∧
  Tendsto (fun k => (codes k).error) atTop (nhds 0) ∧
  ∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop, R - delta ≤ (codes k).rate

/-- PDF pp.1-2: nonnegative extended supremum of operationally achievable rates.
The empty set has capacity zero. Positive-dimensional channels admit zero-rate
one-message codes; no finite-dimensional entropy supremum defines this capacity. -/
def operationalCapacity (N : Backward) (restriction : BlockCode N → Prop) : ENNReal :=
  sSup {r | ∃ R : ℝ, (∃ codes, Achieves restriction codes R) ∧ r = ENNReal.ofReal R}

/-- PDF pp.1-2, (6): one arbitrarily large entangled block and no intervening feedback.
Any final local instrument is absorbed in the decoder. This is operational C. -/
def unassistedCapacity (N : Backward) : ENNReal :=
  operationalCapacity N (fun c => c.rounds = 1)

/-- PDF p.4, III.B: arbitrarily large blocks with separable inter-block feedback cuts. -/
def separableFeedbackCapacity (N : Backward) : ENNReal :=
  operationalCapacity N (fun c => c.protocol.SeparableCuts (uniformPrior c.messages))

/-- Sanity: a zero-use tensor block has one-dimensional ports, as an empty tensor product. -/
example (N : Backward) :
    (forwardTensorBlock N 0).input = 1 ∧ (forwardTensorBlock N 0).output = 1 := by
  simp [forwardTensorBlock]

/-- Sanity: the message flag is untouched, and its diagonal block has the given prior. -/
example {A B : Type} {M : ℕ} (p : Fin M → ℝ)
    (X : Fin M → Matrix (A × B) (A × B) ℂ) (m : Fin M)
    (a aa : A) (b bb : B) :
    cutState p X ((m,b),a) ((m,bb),aa) = (p m : ℂ) * X m (a,b) (aa,bb) := by
  simp [cutState]

/-- Sanity: the initial receiver has no shared resource and no message-dependent seed. -/
example {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M) (m : Fin M) :
    P.state m 0 = Matrix.kronecker (P.aliceInitial m) P.bobInitial := rfl

/-- Sanity: no forward call occurs in a zero-round code. Such codes are not valid. -/
example {N : Backward} (c : BlockCode N) (h : c.rounds = 0) : c.uses = 0 := by
  simp [BlockCode.uses, h]

/-- Sanity: impossible feedback outcomes give a zero branch, without normalization. -/
example {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (m : Fin M) (history : ℕ → ℕ) (j : ℕ) (h : ¬ history j < P.outcomes j) :
    P.branchState m history (j+1) = 0 := by
  simp [FeedbackExecution.branchState, h]

/-- Sanity: the automatic feedback record is classical, with zero coherence
between different histories; no coherent quantum feedback is introduced. -/
example {ch : ℕ → Backward} {n M : ℕ} (P : FeedbackExecution ch n M)
    (m : Fin M) (j : ℕ) (a aa : Fin (P.aliceDim j))
    (h hh : P.History j) (b bb : Fin (P.bobDim j)) (hne : h ≠ hh) :
    P.recordedState m j (a,(h,b)) (aa,(hh,bb)) = 0 := by
  simp [FeedbackExecution.recordedState, hne]

/-- Sanity: the single-block class permits arbitrary entanglement within the block,
but has no inter-block feedback cut. -/
example {ch : ℕ → Backward} {M : ℕ} (P : FeedbackExecution ch 1 M) (p : Fin M → ℝ) :
    P.SeparableCuts p := by
  intro j h
  omega

/-- Sanity: the one-message operational prior is one, and its numerator rate is zero. -/
example (m : Fin 1) : uniformPrior 1 m = 1 ∧ Real.logb 2 (1 : ℝ) = 0 := by
  simp [uniformPrior]

end QAlgorithms.Papers.Independent.Frontier30.P06


