-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08
-- name    : QAlgorithms_Papers_Independent_Claimed50_P08
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:13:27.319843+00:00
-- url     : https://prove2.me/theorems/49c2ec9d-b1d5-49b1-a6fc-80af96f17e12
-- title:
--   Definitions for Hadamard quantum broadcast channels
-- statement:
--   The objects the formalized statements of *Hadamard quantum broadcast channels* (arXiv:1611.07651) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BroadcastRegister`: PDF pp.2–3: a nonzero finite register, dimension d+1, in a fixed basis.
--   - `BroadcastBlock`: PDF pp.3,9,12: the register of n uses, including entangled block inputs.
--   - `HadamardData`: PDF p.2, (1): POVM vectors and unit prepared vectors. The phi vectors need not have unit norm.
--   - `inputIsometry`: PDF p.2, (1): U|v> = sum_x |x>|psi_x><phi_x|v>.
--   - `hadamardChannel`: PDF p.2, (1): the concrete broadcast channel on all operators.
--   - `bobChannel`: PDF p.3, (2): Bob's marginal.
--   - `charlieChannel`: PDF p.3, (4): Charlie's marginal.
--   - `inputCoefficient`: PDF p.2, (1): <phi_x|sigma|phi_y>; the bra is conjugated.
--   - `isometricRecovery`: PDF p.2: isometricRecovery applies U adjoint on its image and replaces its orthogonal complement by |0><0|, making isometricRecovery trace preserving on all operators.
--   - `degradingIsometry`: PDF p.3, (6): copy the basis label to Y and prepare psi_x on Cprime. Cprime is identified with C by the fixed isomorphism.
--   - `basisMeasurement`: PDF p.3, below (7): basis measurement B to Y. Both bases are BroadcastRegister b; this corrects the printed Y subscript on the input side.
--   - `hadamardPreparation`: PDF p.3, (8): prepare psi_x from the classical Y label.
--   - `degradingChannel`: PDF p.3, (7)–(8): discard BY after Bob's isometry.
--   - `ClassicalEnsemble`: PDF p.4, (13): joint WZ distribution and normalized inputs depending on z only.
--   - `ClassicalEnsemble.Pure`: PDF p.4, (21): all conditional inputs are pure in the capacity normal form.
--   - `cqBlocks`: BroadcastBlock diagonal cq operator with subnormalized blocks; no division by zero weights.
--   - `classicalEntropy`: Classical entropy in bits, through the diagonal density.
--   - `classicalConditionalInfo`: PDF p.4, (13)–(18): I(Z;O|W)=H(WZ)+H(WO)-H(W)-H(WZO), in the actual output.
--   - `classicalLayerInfo`: PDF p.4: I(W;O)=H(W)+H(O)-H(WO), in the same ensemble.
--   - `classicalTotalInfo`: PDF p.4, (12): I(Z;O) using the same distribution's Z marginal.
--   - `ReferenceEnsemble`: PDF pp.10,12–13: W ensemble with arbitrary finite reference R. Mixed conditional states are allowed; purity is separate.
--   - `ReferenceEnsemble.Pure`: PDF pp.10,13, (73),(103): purity of every conditional RA state.
--   - `referenceBob`: Actual RB output marginal, preserving reference off-diagonal entries.
--   - `referenceCharlie`: Charlie's output marginal of a conditional RA input.
--   - `referenceMutualInfo`: PDF pp.12–13, (97),(101): conditional mutual information; no factor one half.
--   - `referenceCoherentInfo`: PDF pp.9–10, (68),(71): coherent information I(R coherent-to BW), the classical average of H(B)-H(RB).
--   - `holevoInfo`: Holevo information in bits.
--   - `referenceBobLayer`: PDF pp.9–13: I(W;B) for the actual channel outputs.
--   - `referenceCharlieLayer`: PDF pp.9–13: I(W;C) for the same ensemble and actual channel outputs.
--   - `BroadcastClassicalCode`: PDF p.3, (9), and p.16, Remark 7: unassisted classical code, with common message dimension k+1, Bob-private u+1, Charlie-private v+1. All three are independent and uniform. Codewords may be mixed and entangled across the n channel uses.
--   - `BroadcastClassicalCode.success`: PDF p.3, (9), and p.16: average JOINT success, including both common copies.
--   - `BobAssistedCode`: PDF p.12, (96), and p.16: arbitrary finite, possibly mixed assistance shared ONLY by Alice and Bob, independent of all messages. Alice's CPTP encoder depends on the messages; Charlie has no assistance register.
--   - `BobAssistedCode.received`: PDF p.12, (96): actual assisted receiver state after encoding and n uses. Coordinates are (Bob's retained resource, B^n), C^n.
--   - `BobAssistedCode.success`: PDF p.12, (96), and p.16: independent-message average JOINT success.
--   - `ClassicalQuantumCode`: PDF p.9, (65)–(67), and p.16: unassisted classical–quantum code. The quantum reference dimension is u+1. Bob's local CPTP decoder returns his common-message label and quantum output. Charlie measures common and private labels. For k=0 these are exactly the two-task codes of Section 4.1.
--   - `CQLabels`: Classical labels: original (common,Charlie-private), Bob's decoded common, Charlie's decoded (common,private). The remaining factors are reference and quantum output.
--   - `ClassicalQuantumCode.branch`: PDF p.9, (66), and p.16: subnormalized RRhat branch, conditioned on actual classical labels. The final partial trace contracts the Charlie POVM, retaining reference/quantum coherence. Bob's common output is measured in its fixed basis.
--   - `ClassicalQuantumCode.decoded`: PDF p.9, (65)–(66), and p.16: normalized JOINT decoded state. The message average is 1/((k+1)(v+1)), correcting 1/M_B to 1/M_C in printed (65),(75). No restriction equating quantum dimension and classical cardinality is imposed.
--   - `cqTarget`: PDF p.9, (67), and p.16: ideal common copies, private Charlie copy, and rank-(u+1) maximally entangled RRhat state, jointly and independently.
--   - `ClassicalQuantumCode.error`: PDF p.9, (67): HALF trace norm of the JOINT target-minus-decoded state.
--   - `CommunicationTask`: The three operational tasks of Sections 3,4,5; the distinction controls codes.
--   - `hasCode`: PDF pp.3,9,12,16: existence of a real n-use code with the specified integer message/reference dimensions. d(0),d(1),d(2) are dimensions minus one for Bob, Charlie-private and common. Each error condition is the source's joint criterion.
--   - `codeRate`: PDF pp.3,9,12: per-use bit/qubit rate of an integer dimension d+1.
--   - `achievable`: PDF pp.3,9,12,16: for every error 0<epsilon<1 and slack delta>0, all sufficiently large POSITIVE blocklengths admit codes meeting every rate bound. When common=false the common message is a singleton at every blocklength. Assistance dimensions are unrestricted code fields and can grow with n.
--   - `pairAchievable`: The genuine two-coordinate achievable region (no common message resource).
--   - `pairCapacity`: PDF pp.3,9,12: Euclidean closure of the operational two-task achievable rates.
--   - `commonCapacity`: PDF p.16, Remark 7: Euclidean closure using actual independent common-message codes.
--   - `classicalRegion`: PDF p.4, (19)–(21), and p.16: one shared pure ensemble witnesses both bounds. No regularization, extra sum constraint, RHS closure or cardinality cap.
--   - `classicalQuantumRegion`: PDF p.10, (71)–(73), and p.16: conditional coherent-information region; the arbitrary finite reference dimension and W are existentially quantified.
--   - `partiallyAssistedRegion`: PDF p.13, (101)–(103), and p.16: conditional MUTUAL-information region for Bob-only entanglement assistance, with no assistance consumption constraint.
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, https://arxiv.org/abs/1611.07651v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-!
Hadamard quantum broadcast channels, arXiv:1611.07651v3. All locators are PDF pages.
Registers have arbitrary positive dimensions d+1; zero means a singleton.
Information and rates use base two. Codes permit arbitrary mixed block inputs,
independent uniform messages, separate receivers and JOINT error criteria.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)
open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF pp.2–3: a nonzero finite register, dimension d+1, in a fixed basis. -/
abbrev BroadcastRegister (d : ℕ) := Fin (d + 1)

/-- PDF pp.3,9,12: the register of n uses, including entangled block inputs. -/
abbrev BroadcastBlock (d n : ℕ) := Fin n → BroadcastRegister d

/-- PDF p.2, (1): POVM vectors and unit prepared vectors.
The phi vectors need not have unit norm. -/
structure HadamardData (a b c : ℕ) where
  phi : BroadcastRegister b → EuclideanSpace ℂ (BroadcastRegister a)
  psi : BroadcastRegister b → EuclideanSpace ℂ (BroadcastRegister c)
  povm : ∑ x, pureDensity (phi x) = 1
  unit : ∀ x, IsState (psi x)

/-- PDF p.2, (1): U|v> = sum_x |x>|psi_x><phi_x|v>. -/
def inputIsometry {a b c : ℕ} (H : HadamardData a b c) :
    Matrix (BroadcastRegister b × BroadcastRegister c) (BroadcastRegister a) ℂ :=
  fun x i => H.psi x.1 x.2 * conj (H.phi x.1 i)

/-- PDF p.2, (1): the concrete broadcast channel on all operators. -/
def hadamardChannel {a b c : ℕ} (H : HadamardData a b c) :
    Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c) := conjSuperop (inputIsometry H)

/-- PDF p.3, (2): Bob's marginal. -/
def bobChannel {a b c : ℕ} (H : HadamardData a b c) : Superop (BroadcastRegister a) (BroadcastRegister b) :=
  traceRight ∘ hadamardChannel H

/-- PDF p.3, (4): Charlie's marginal. -/
def charlieChannel {a b c : ℕ} (H : HadamardData a b c) : Superop (BroadcastRegister a) (BroadcastRegister c) :=
  traceLeft ∘ hadamardChannel H

/-- PDF p.2, (1): <phi_x|sigma|phi_y>; the bra is conjugated. -/
def inputCoefficient {a b c : ℕ} (H : HadamardData a b c) (sigma : Op (BroadcastRegister a))
    (x y : BroadcastRegister b) : ℂ :=
  ∑ i, ∑ j, conj (H.phi x i) * sigma i j * H.phi y j

/-- PDF p.2: isometricRecovery applies U adjoint on its image and replaces its orthogonal
complement by |0><0|, making isometricRecovery trace preserving on all operators. -/
def isometricRecovery {a b c : ℕ} (H : HadamardData a b c) :
    Superop (BroadcastRegister b × BroadcastRegister c) (BroadcastRegister a) :=
  fun rho =>
    let compressed := (inputIsometry H)ᴴ * rho * inputIsometry H
    compressed + (rho.trace - compressed.trace) • pureDensity (ket (0 : BroadcastRegister a))

/-- PDF p.3, (6): copy the basis label to Y and prepare psi_x on Cprime.
Cprime is identified with C by the fixed isomorphism. -/
def degradingIsometry {a b c : ℕ} (H : HadamardData a b c) :
    Matrix ((BroadcastRegister b × BroadcastRegister b) × BroadcastRegister c) (BroadcastRegister b) ℂ :=
  fun p x => if p.1.1 = x ∧ p.1.2 = x then H.psi x p.2 else 0

/-- PDF p.3, below (7): basis measurement B to Y. Both bases are BroadcastRegister b;
this corrects the printed Y subscript on the input side. -/
def basisMeasurement {b : ℕ} : Superop (BroadcastRegister b) (BroadcastRegister b) :=
  fun rho => Matrix.diagonal fun x => rho x x

/-- PDF p.3, (8): prepare psi_x from the classical Y label. -/
def hadamardPreparation {a b c : ℕ} (H : HadamardData a b c) : Superop (BroadcastRegister b) (BroadcastRegister c) :=
  fun rho => ∑ x, rho x x • pureDensity (H.psi x)

/-- PDF p.3, (7)–(8): discard BY after Bob's isometry. -/
def degradingChannel {a b c : ℕ} (H : HadamardData a b c) : Superop (BroadcastRegister b) (BroadcastRegister c) :=
  traceLeft ∘ conjSuperop (degradingIsometry H)

/-- PDF p.4, (13): joint WZ distribution and normalized inputs depending on z only. -/
structure ClassicalEnsemble (w z a : ℕ) where
  probability : Distribution (BroadcastRegister w × BroadcastRegister z)
  state : BroadcastRegister z → Op (BroadcastRegister a)
  density : ∀ j, IsDensityMatrix (state j)

/-- PDF p.4, (21): all conditional inputs are pure in the capacity normal form. -/
def ClassicalEnsemble.Pure {w z a : ℕ} (S : ClassicalEnsemble w z a) : Prop :=
  ∀ j, ∃ v : EuclideanSpace ℂ (BroadcastRegister a), IsState v ∧ S.state j = pureDensity v

/-- BroadcastBlock diagonal cq operator with subnormalized blocks; no division by zero weights. -/
def cqBlocks {W I : Type} [DecidableEq W] (rho : W → Op I) : Op (W × I) :=
  fun p q => if p.1 = q.1 then rho p.1 p.2 q.2 else 0

/-- Classical entropy in bits, through the diagonal density. -/
def classicalEntropy {I : Type} [Fintype I] [DecidableEq I] (p : I → ℝ) : ℝ :=
  vnEntropy (Matrix.diagonal fun i => (p i : ℂ))

/-- PDF p.4, (13)–(18): I(Z;O|W)=H(WZ)+H(WO)-H(W)-H(WZO), in the actual output. -/
def classicalConditionalInfo {w z a : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (S : ClassicalEnsemble w z a) (F : Superop (BroadcastRegister a) O) : ℝ :=
  let p := S.probability.val
  classicalEntropy p +
    vnEntropy (cqBlocks fun i : BroadcastRegister w => ∑ j : BroadcastRegister z, (p (i, j) : ℂ) • F (S.state j)) -
    classicalEntropy (fun i : BroadcastRegister w => ∑ j : BroadcastRegister z, p (i, j)) -
    vnEntropy (cqBlocks fun ij : BroadcastRegister w × BroadcastRegister z => (p ij : ℂ) • F (S.state ij.2))

/-- PDF p.4: I(W;O)=H(W)+H(O)-H(WO), in the same ensemble. -/
def classicalLayerInfo {w z a : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (S : ClassicalEnsemble w z a) (F : Superop (BroadcastRegister a) O) : ℝ :=
  let p := S.probability.val
  classicalEntropy (fun i : BroadcastRegister w => ∑ j : BroadcastRegister z, p (i, j)) +
    vnEntropy (∑ i : BroadcastRegister w, ∑ j : BroadcastRegister z, (p (i, j) : ℂ) • F (S.state j)) -
    vnEntropy (cqBlocks fun i : BroadcastRegister w => ∑ j : BroadcastRegister z, (p (i, j) : ℂ) • F (S.state j))

/-- PDF p.4, (12): I(Z;O) using the same distribution's Z marginal. -/
def classicalTotalInfo {w z a : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (S : ClassicalEnsemble w z a) (F : Superop (BroadcastRegister a) O) : ℝ :=
  let p := fun j : BroadcastRegister z => ∑ i : BroadcastRegister w, S.probability.val (i, j)
  classicalEntropy p + vnEntropy (∑ j, (p j : ℂ) • F (S.state j)) -
    vnEntropy (cqBlocks fun j => (p j : ℂ) • F (S.state j))

/-- PDF pp.10,12–13: W ensemble with arbitrary finite reference R.
Mixed conditional states are allowed; purity is separate. -/
structure ReferenceEnsemble (w r a : ℕ) where
  probability : Distribution (BroadcastRegister w)
  state : BroadcastRegister w → Op (BroadcastRegister r × BroadcastRegister a)
  density : ∀ j, IsDensityMatrix (state j)

/-- PDF pp.10,13, (73),(103): purity of every conditional RA state. -/
def ReferenceEnsemble.Pure {w r a : ℕ} (S : ReferenceEnsemble w r a) : Prop :=
  ∀ j, ∃ v : EuclideanSpace ℂ (BroadcastRegister r × BroadcastRegister a), IsState v ∧ S.state j = pureDensity v

/-- Actual RB output marginal, preserving reference off-diagonal entries. -/
def referenceBob {a b c r : ℕ} (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c))
    (rho : Op (BroadcastRegister r × BroadcastRegister a)) : Op (BroadcastRegister r × BroadcastRegister b) :=
  fun p q => ∑ k : BroadcastRegister c, idTensorSuperop N rho (p.1, (p.2, k)) (q.1, (q.2, k))

/-- Charlie's output marginal of a conditional RA input. -/
def referenceCharlie {a b c r : ℕ} (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c))
    (rho : Op (BroadcastRegister r × BroadcastRegister a)) : Op (BroadcastRegister c) :=
  traceLeft (traceLeft (idTensorSuperop N rho))

/-- PDF pp.12–13, (97),(101): conditional mutual information; no factor one half. -/
def referenceMutualInfo {w r a b c : ℕ} (S : ReferenceEnsemble w r a)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : ℝ :=
  ∑ j, S.probability.val j *
    (vnEntropy (traceRight (referenceBob N (S.state j))) +
      vnEntropy (traceLeft (referenceBob N (S.state j))) - vnEntropy (referenceBob N (S.state j)))

/-- PDF pp.9–10, (68),(71): coherent information I(R coherent-to BW),
the classical average of H(B)-H(RB). -/
def referenceCoherentInfo {w r a b c : ℕ} (S : ReferenceEnsemble w r a)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : ℝ :=
  ∑ j, S.probability.val j *
    (vnEntropy (traceLeft (referenceBob N (S.state j))) - vnEntropy (referenceBob N (S.state j)))

/-- Holevo information in bits. -/
def holevoInfo {W I : Type} [Fintype W] [Fintype I] [DecidableEq I]
    (p : W → ℝ) (rho : W → Op I) : ℝ :=
  vnEntropy (∑ j, (p j : ℂ) • rho j) - ∑ j, p j * vnEntropy (rho j)

/-- PDF pp.9–13: I(W;B) for the actual channel outputs. -/
def referenceBobLayer {w r a b c : ℕ} (S : ReferenceEnsemble w r a)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : ℝ :=
  holevoInfo S.probability.val fun j => traceLeft (referenceBob N (S.state j))

/-- PDF pp.9–13: I(W;C) for the same ensemble and actual channel outputs. -/
def referenceCharlieLayer {w r a b c : ℕ} (S : ReferenceEnsemble w r a)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : ℝ :=
  holevoInfo S.probability.val fun j => referenceCharlie N (S.state j)

/-- PDF p.3, (9), and p.16, Remark 7: unassisted classical code, with common
message dimension k+1, Bob-private u+1, Charlie-private v+1. All three are independent
and uniform. Codewords may be mixed and entangled across the n channel uses. -/
structure BroadcastClassicalCode (a b c n k u v : ℕ) where
  word : BroadcastRegister k → BroadcastRegister u → BroadcastRegister v → Op (BroadcastBlock a n)
  density : ∀ s i j, IsDensityMatrix (word s i j)
  bob : (BroadcastRegister k × BroadcastRegister u) → Op (BroadcastBlock b n)
  bob_povm : IsPOVM bob
  charlie : (BroadcastRegister k × BroadcastRegister v) → Op (BroadcastBlock c n)
  charlie_povm : IsPOVM charlie

/-- PDF p.3, (9), and p.16: average JOINT success, including both common copies. -/
def BroadcastClassicalCode.success {a b c n k u v : ℕ} (C : BroadcastClassicalCode a b c n k u v)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : ℝ :=
  (∑ s : BroadcastRegister k, ∑ i : BroadcastRegister u, ∑ j : BroadcastRegister v,
    effectProb (Matrix.kronecker (C.bob (s, i)) (C.charlie (s, j)))
      (groupedChannelPower N n (C.word s i j))) /
    (((k + 1 : ℕ) : ℝ) * ((u + 1 : ℕ) : ℝ) * ((v + 1 : ℕ) : ℝ))

/-- PDF p.12, (96), and p.16: arbitrary finite, possibly mixed assistance shared
ONLY by Alice and Bob, independent of all messages. Alice's CPTP encoder depends
on the messages; Charlie has no assistance register. -/
structure BobAssistedCode (a b c n k u v : ℕ) where
  bobResource : ℕ
  aliceResource : ℕ
  shared : Op (BroadcastRegister bobResource × BroadcastRegister aliceResource)
  shared_density : IsDensityMatrix shared
  encoder : BroadcastRegister k → BroadcastRegister u → BroadcastRegister v → Superop (BroadcastRegister aliceResource) (BroadcastBlock a n)
  encoder_cptp : ∀ s i j, IsChannel (encoder s i j)
  bob : (BroadcastRegister k × BroadcastRegister u) → Op (BroadcastRegister bobResource × BroadcastBlock b n)
  bob_povm : IsPOVM bob
  charlie : (BroadcastRegister k × BroadcastRegister v) → Op (BroadcastBlock c n)
  charlie_povm : IsPOVM charlie

/-- PDF p.12, (96): actual assisted receiver state after encoding and n uses.
Coordinates are (Bob's retained resource, B^n), C^n. -/
def BobAssistedCode.received {a b c n k u v : ℕ} (C : BobAssistedCode a b c n k u v)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) (s : BroadcastRegister k) (i : BroadcastRegister u) (j : BroadcastRegister v) :
    Op ((BroadcastRegister C.bobResource × BroadcastBlock b n) × BroadcastBlock c n) :=
  let rho := idTensorSuperop (groupedChannelPower N n)
    (idTensorSuperop (C.encoder s i j) C.shared)
  fun p q => rho (p.1.1, (p.1.2, p.2)) (q.1.1, (q.1.2, q.2))

/-- PDF p.12, (96), and p.16: independent-message average JOINT success. -/
def BobAssistedCode.success {a b c n k u v : ℕ} (C : BobAssistedCode a b c n k u v)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : ℝ :=
  (∑ s : BroadcastRegister k, ∑ i : BroadcastRegister u, ∑ j : BroadcastRegister v,
    effectProb (Matrix.kronecker (C.bob (s, i)) (C.charlie (s, j))) (C.received N s i j)) /
    (((k + 1 : ℕ) : ℝ) * ((u + 1 : ℕ) : ℝ) * ((v + 1 : ℕ) : ℝ))

/-- PDF p.9, (65)–(67), and p.16: unassisted classical–quantum code.
The quantum reference dimension is u+1. Bob's local CPTP decoder returns his
common-message label and quantum output. Charlie measures common and private labels.
For k=0 these are exactly the two-task codes of Section 4.1. -/
structure ClassicalQuantumCode (a b c n k u v : ℕ) where
  word : BroadcastRegister k → BroadcastRegister v → Op (BroadcastRegister u × BroadcastBlock a n)
  density : ∀ s j, IsDensityMatrix (word s j)
  decoder : Superop (BroadcastBlock b n) (BroadcastRegister k × BroadcastRegister u)
  decoder_cptp : IsChannel decoder
  charlie : (BroadcastRegister k × BroadcastRegister v) → Op (BroadcastBlock c n)
  charlie_povm : IsPOVM charlie

/-- Classical labels: original (common,Charlie-private), Bob's decoded common,
Charlie's decoded (common,private). The remaining factors are reference and quantum output. -/
abbrev CQLabels (k v : ℕ) := (BroadcastRegister k × BroadcastRegister v) × (BroadcastRegister k × (BroadcastRegister k × BroadcastRegister v))

/-- PDF p.9, (66), and p.16: subnormalized RRhat branch, conditioned on actual
classical labels. The final partial trace contracts the Charlie POVM, retaining
reference/quantum coherence. Bob's common output is measured in its fixed basis. -/
def ClassicalQuantumCode.branch {a b c n k u v : ℕ}
    (C : ClassicalQuantumCode a b c n k u v) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c))
    (s : BroadcastRegister k) (j : BroadcastRegister v) (h : BroadcastRegister k) (g : BroadcastRegister k × BroadcastRegister v) : Op (BroadcastRegister u × BroadcastRegister u) :=
  let received := idTensorSuperop (groupedChannelPower N n) (C.word s j)
  let decoded := idTensorSuperop (mapFirst C.decoder) received
  fun p q => ∑ x : BroadcastBlock c n, ∑ y : BroadcastBlock c n,
    C.charlie g y x * decoded (p.1, ((h, p.2), x)) (q.1, ((h, q.2), y))

/-- PDF p.9, (65)–(66), and p.16: normalized JOINT decoded state. The message
average is 1/((k+1)(v+1)), correcting 1/M_B to 1/M_C in printed (65),(75).
No restriction equating quantum dimension and classical cardinality is imposed. -/
def ClassicalQuantumCode.decoded {a b c n k u v : ℕ}
    (C : ClassicalQuantumCode a b c n k u v) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) :
    Op (CQLabels k v × (BroadcastRegister u × BroadcastRegister u)) :=
  fun p q => if p.1 = q.1 then
    ((((k + 1 : ℕ) : ℂ) * ((v + 1 : ℕ) : ℂ))⁻¹) *
      C.branch N p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2 q.2
    else 0

/-- PDF p.9, (67), and p.16: ideal common copies, private Charlie copy, and
rank-(u+1) maximally entangled RRhat state, jointly and independently. -/
def cqTarget (k u v : ℕ) : Op (CQLabels k v × (BroadcastRegister u × BroadcastRegister u)) :=
  fun p q => if p.1 = q.1 ∧ p.1.1.1 = p.1.2.1 ∧
      p.1.1.1 = p.1.2.2.1 ∧ p.1.1.2 = p.1.2.2.2 then
    ((((k + 1 : ℕ) : ℂ) * ((v + 1 : ℕ) : ℂ))⁻¹) *
      pureDensity (finiteMaxEntangled (BroadcastRegister u)) p.2 q.2
    else 0

/-- PDF p.9, (67): HALF trace norm of the JOINT target-minus-decoded state. -/
def ClassicalQuantumCode.error {a b c n k u v : ℕ}
    (C : ClassicalQuantumCode a b c n k u v) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (cqTarget k u v - C.decoded N)

/-- The three operational tasks of Sections 3,4,5; the distinction controls codes. -/
inductive CommunicationTask where
  | classical
  | classicalQuantum
  | partiallyAssisted

/-- PDF pp.3,9,12,16: existence of a real n-use code with the specified integer
message/reference dimensions. d(0),d(1),d(2) are dimensions minus one for Bob,
Charlie-private and common. Each error condition is the source's joint criterion. -/
def hasCode {a b c : ℕ} (mode : CommunicationTask) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c))
    (n : ℕ) (d : Fin 3 → ℕ) (epsilon : ℝ) : Prop :=
  0 < n ∧ 0 ≤ epsilon ∧ epsilon ≤ 1 ∧
  match mode with
  | .classical => ∃ C : BroadcastClassicalCode a b c n (d 2) (d 0) (d 1), 1 - epsilon ≤ C.success N
  | .classicalQuantum => ∃ C : ClassicalQuantumCode a b c n (d 2) (d 0) (d 1), C.error N ≤ epsilon
  | .partiallyAssisted => ∃ C : BobAssistedCode a b c n (d 2) (d 0) (d 1), 1 - epsilon ≤ C.success N

/-- PDF pp.3,9,12: per-use bit/qubit rate of an integer dimension d+1. -/
def codeRate (d n : ℕ) : ℝ := Real.logb 2 (d + 1 : ℕ) / (n : ℝ)

/-- PDF pp.3,9,12,16: for every error 0<epsilon<1 and slack delta>0, all
sufficiently large POSITIVE blocklengths admit codes meeting every rate bound.
When common=false the common message is a singleton at every blocklength.
Assistance dimensions are unrestricted code fields and can grow with n. -/
def achievable {a b c : ℕ} (mode : CommunicationTask) (common : Bool)
    (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) : Set (Fin 3 → ℝ) :=
  {r | (∀ j, 0 ≤ r j) ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∀ delta : ℝ, 0 < delta →
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
        ∃ d : Fin 3 → ℕ, (common = true ∨ d 2 = 0) ∧ hasCode mode N n d epsilon ∧
          ∀ j : Fin 3, r j - delta ≤ codeRate (d j) n}

/-- The genuine two-coordinate achievable region (no common message resource). -/
def pairAchievable {a b c : ℕ} (mode : CommunicationTask) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) :
    Set (ℝ × ℝ) := {r | (![r.1, r.2, 0] : Fin 3 → ℝ) ∈ achievable mode false N}

/-- PDF pp.3,9,12: Euclidean closure of the operational two-task achievable rates. -/
def pairCapacity {a b c : ℕ} (mode : CommunicationTask) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) :
    Set (ℝ × ℝ) := closure (pairAchievable mode N)

/-- PDF p.16, Remark 7: Euclidean closure using actual independent common-message codes. -/
def commonCapacity {a b c : ℕ} (mode : CommunicationTask) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) :
    Set (Fin 3 → ℝ) := closure (achievable mode true N)

/-- PDF p.4, (19)–(21), and p.16: one shared pure ensemble witnesses both
bounds. No regularization, extra sum constraint, RHS closure or cardinality cap. -/
def classicalRegion {a b c : ℕ} (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c))
    (rates : ℝ × ℝ) (common : ℝ) : Prop :=
  0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧ 0 ≤ common ∧
    ∃ w z : ℕ, ∃ S : ClassicalEnsemble w z a, S.Pure ∧
      rates.1 ≤ classicalConditionalInfo S (traceRight ∘ N) ∧
      common + rates.2 ≤ classicalLayerInfo S (traceLeft ∘ N)

/-- PDF p.10, (71)–(73), and p.16: conditional coherent-information region;
the arbitrary finite reference dimension and W are existentially quantified. -/
def classicalQuantumRegion {a b c : ℕ} (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c))
    (rates : ℝ × ℝ) (common : ℝ) : Prop :=
  0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧ 0 ≤ common ∧
    ∃ w r : ℕ, ∃ S : ReferenceEnsemble w r a, S.Pure ∧
      rates.1 ≤ referenceCoherentInfo S N ∧ common + rates.2 ≤ referenceCharlieLayer S N

/-- PDF p.13, (101)–(103), and p.16: conditional MUTUAL-information region
for Bob-only entanglement assistance, with no assistance consumption constraint. -/
def partiallyAssistedRegion {a b c : ℕ} (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c))
    (rates : ℝ × ℝ) (common : ℝ) : Prop :=
  0 ≤ rates.1 ∧ 0 ≤ rates.2 ∧ 0 ≤ common ∧
    ∃ w r : ℕ, ∃ S : ReferenceEnsemble w r a, S.Pure ∧
      rates.1 ≤ referenceMutualInfo S N ∧ common + rates.2 ≤ referenceCharlieLayer S N

/-! Sanity checks on local definitions: these are small interface checks, not
proofs of the seven source results. Compilation is pending the batch handoff. -/

/-- Singleton dimensions remain nonempty, including all auxiliary registers. -/
example : Fintype.card (BroadcastRegister 0) = 1 := by decide

/-- A singleton message has zero rate; n=0 is never used by achievable. -/
example (n : ℕ) : codeRate 0 n = 0 := by simp [codeRate]

/-- The zero-use block has one input/output basis configuration, not an empty space. -/
example (a b c : ℕ) (N : Superop (BroadcastRegister a) (BroadcastRegister b × BroadcastRegister c)) (rho : Op (BroadcastBlock a 0))
    (p q : BroadcastBlock b 0 × BroadcastBlock c 0) :
    groupedChannelPower N 0 rho p q = rho (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) := by
  simp [groupedChannelPower, piSuperop]
  exact congrArg₂ rho (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- Fixed basis measurement preserves diagonals. -/
example {b : ℕ} (rho : Op (BroadcastRegister b)) (x : BroadcastRegister b) : basisMeasurement rho x x = rho x x := by
  simp [basisMeasurement]

/-- The copying/preparation isometry sends basis x to |x,x> times psi_x. -/
example {a b c : ℕ} (H : HadamardData a b c) (x : BroadcastRegister b) (j : BroadcastRegister c) :
    degradingIsometry H ((x, x), j) x = H.psi x j := by
  simp [degradingIsometry]

/-- Identity extension on the first factor preserves all joint matrix entries. -/
example {I K : Type} (rho : Op (I × K)) : mapFirst (fun x : Op I => x) rho = rho := by
  rfl

/-- Diagonal cq blocks retain the conditional quantum state. -/
example {W I : Type} [DecidableEq W] (rho : W → Op I) (w : W) (i j : I) :
    cqBlocks rho (w, i) (w, j) = rho w i j := by
  simp [cqBlocks]

/-- Distinct classical blocks cannot retain off-diagonal coherence. -/
example {W I : Type} [DecidableEq W] (rho : W → Op I) (w v : W) (h : w ≠ v) (i j : I) :
    cqBlocks rho (w, i) (v, j) = 0 := by
  simp [cqBlocks, h]

/-- Empty classical weights have zero entropy, with the intended 0 log 0 convention. -/
example {I : Type} [Fintype I] [DecidableEq I] : classicalEntropy (fun _ : I => 0) = 0 := by
  simp [classicalEntropy, vnEntropy, cfc_zero]

/-- Rank-one maximally entangled target has a unit entry in singleton dimensions. -/
example : cqTarget 0 0 0 (((0, 0), (0, (0, 0))), (0, 0))
    (((0, 0), (0, (0, 0))), (0, 0)) = 1 := by
  simp [cqTarget, finiteMaxEntangled, pureDensity, BroadcastRegister]

end QAlgorithms.Papers.Independent.Claimed50.P08


