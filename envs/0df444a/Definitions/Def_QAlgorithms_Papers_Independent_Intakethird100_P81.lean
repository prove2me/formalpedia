-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P81
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:54:49.976014+00:00
-- url     : https://prove2.me/theorems/6f7637b7-4874-409f-ab66-e19212d0a79d
-- title:
--   Definitions for On rounds in quantum communication
-- statement:
--   The objects the formalized statements of *On rounds in quantum communication* (arXiv:quant-ph/0004100) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `jointMutualInfoBits`: Definition 8, p.8: mutual information in bits, with both marginals computed from rho.
--   - `jointMarginalProduct`: P.11: the product of the actual marginals, never an unrelated state parameter.
--   - `informationalDistance`: P.11: informational distance is the FULL trace norm, without a half factor.
--   - `swapState`: P.11, Lemma 2.1: exchange the named tensor factors.
--   - `classicalWeight`: Pp.11–12: probability of a classical A outcome.
--   - `firstRegisterConditionalBlock`: Pp.11–12: the normalized conditional B state; the zero-probability branch is set to zero and is always multiplied by its zero probability in Lemma 3.2.
--   - `agreement`: P.11, Lemma 3.1: jointly measure a Boolean POVM on A and the standard basis on B.
--   - `PointerMap`: Definition 11, PDF p.12: unrestricted two-sided functional graph. Both input tables have n entries, each in Fin n; the two copies are separately owned.
--   - `Vertex`: The disjoint labelled vertex sets, with standard labels 0,...,n-1 and n,...,2n-1.
--   - `successor`: Definition 11, PDF p.12: no injectivity or acyclicity promise.
--   - `endpoint`: Definition 11, PDF p.12: the endpoint follows k+1 pointers from the fixed Alice vertex.
--   - `vertexLabel`: Definition 11, PDF p.12: standard binary code of the disjoint vertex labels.
--   - `pointerParity`: Definition 11, PDF p.12: XOR of ALL binary bits, independent of leading zero padding.
--   - `nonDisjoint`: Section 6, PDF p.19: the source's DISJ accepts intersecting sets.
--   - `iteratedLog`: P.13: saturated real iterated binary logarithm; the zeroth iterate is n.
--   - `logStar`: P.13: least iteration reaching one. For positive finite integer n this set is nonempty; all resource statements exclude n<2.
--   - `ClassicalTree`: Definition 4, pp.5–6: a finite deterministic binary protocol with local output.
--   - `ClassicalTree.run`: Definition 4, pp.5–6: execution follows the local input at each transcript node.
--   - `ClassicalTree.cost`: Definition 4, pp.5–6: worst-case transmitted bits; local announcements cost nothing. Unused branches can be pruned, so this presents every finite worst-case protocol.
--   - `ClassicalTree.changes`: P.6: number of subsequent speaker changes along the worst branch.
--   - `ClassicalTree.rounds`: P.6: at most k messages with the specified starter, allowing empty padding.
--   - `PublicProtocol`: Definition 4: the public randomness is independent of both inputs. Finite input/cost protocols have only finitely many distinct deterministic trees, so grouping seeds loses nothing.
--   - `PublicProtocol.bounded`: Definition 4: worst-case communication and rounds on every public seed of positive weight.
--   - `PublicProtocol.computes`: Definition 4: correctness for EVERY input, with the protocol fixed before the input.
--   - `QuantumRound`: Definition 5, p.6: one round's fixed speaker/wires and local-input-controlled unitaries.
--   - `QuantumRound.matrix`: Definition 5: the unitary can inspect only its speaker's classical input.
--   - `QuantumRound.update`: Definition 5: transferring a fixed set of owned wires changes ownership, not the state.
--   - `owned`: Owned wire set, used to enforce physical locality, p.6.
--   - `roundsLegal`: Definition 5: all operations and transfers act only on the speaker's owned wires.
--   - `speakerAt`: Alternating messages, p.6; t is zero-based.
--   - `QuantumProtocol`: Definition 5 and Definition 6, pp.6–7: arbitrary finite private and shared workspace. Final announcements are a local measurement and are not charged transmissions.
--   - `QuantumProtocol.ownerAt`: Ownership at the cut after t messages (before message t+1), pp.14–15.
--   - `QuantumProtocol.measurement`: Input-local final POVM, Definition 5.
--   - `QuantumProtocol.valid`: Definition 5: all registers normalized, all transfers legal, exactly k alternating messages (possibly empty), and a local output POVM.
--   - `QuantumProtocol.cost`: Definition 5: structural count of transmitted qubits, never a free cost label.
--   - `QuantumProtocol.stateAt`: Definition 5: actual execution, with all round unitaries fixed before either input.
--   - `QuantumProtocol.probability`: Definition 5: the final local measurement's output distribution.
--   - `QuantumProtocol.computes`: Definition 5: bounded error is a worst-case, per-input guarantee.
--   - `coherentInitial`: P.14, coherent execution for Lemma 7: input registers are explicitly retained, and measurements pinch only actual local computational registers. No remote path access occurs. Uniform coherent input, tensor the normalized input-independent work state. For PointerMap n the normalization factor is exactly 1/n^n.
--   - `controlledRound`: Pp.6,14: input controls are block diagonal and leave BOTH input registers unchanged.
--   - `MeasurementPattern`: Pp.14,18: optional standard-basis measurements of specified physical registers. The X and Y registers belong to Alice and Bob respectively; each work wire has its current owner.
--   - `dephaseSelectedRegisters`: Pp.14,18: nonselective local measurements, keeping all classical values in their registers. This is the product of the owners' local dephasings, with no communicated outcome for free.
--   - `coherentExecutionStateAt`: Pp.14,18: constructed state after t messages, with any chosen local register measurements at each cut. The all-empty pattern is the unmeasured run.
--   - `AliceConfig`: Alice's actual owned work configurations at a cut, pp.14,18.
--   - `BobConfig`: Complementary work configurations; with two parties these are exactly Bob's wires.
--   - `mergeWork`: Recombine local work configurations on the same physical wires.
--   - `aliceInputJoint`: Lemma 7, p.18: the actual (F_A M_A):F_B reduction, tracing out only Bob's WORK wires. Input registers remain in the state and are not replaced by arbitrary marginals.
--   - `LocalChannel`: Definition 2 and the model paragraph p.6: a CPTP operation local to S. The finite normalized Kraus family gives complete positivity, complex linearity and trace preservation.
--   - `ChannelRound`: P.6: a round in the local CPTP model, with fixed sender, transfers and boundaries.
--   - `ChannelRound.operation`: P.6: local classical input control for a general local quantum operation.
--   - `ChannelRound.update`: P.6: changing the owner of exactly the specified sent wires.
--   - `channelRoundsLegal`: P.6: legality ensures there are no remote operations or undeclared transmissions.
--   - `ChannelProtocol`: P.6: the same fixed communication model with local CPTP maps in place of unitaries.
--   - `ChannelProtocol.finalOwner`: P.6: final ownership after all fixed transfers.
--   - `ChannelProtocol.measurement`: P.6: the announcing player's own-input-controlled measurement.
--   - `ChannelProtocol.valid`: P.6: complete validity conditions, including normalization and a local output.
--   - `ChannelProtocol.finalState`: P.6: the actual output density matrix after all local channels and ownership transfers.
--   - `ChannelProtocol.cost`: P.6: the structural communication cost.
--   - `ChannelProtocol.probability`: P.6: the full measured output law to be preserved by simulation.
--   - `BlankExtension`: P.6: additional PRIVATE blank ancillas, rather than stronger prior entanglement or advice. The injection preserves the original ownership and embeds exactly the original initial vector.
--   - `preparationRound`: P.7: Alice prepares the input-independent shared vector on local wires, then sends exactly the wires intended for Bob; the preparation phase is uncharged.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, https://arxiv.org/abs/quant-ph/0004100v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)
open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-! Paper-local interfaces for Klauck, arXiv:quant-ph/0004100v5.
All page numbers below are PDF page numbers. No frozen definition is modified.
-/

/-- Definition 8, p.8: mutual information in bits, with both marginals computed from rho. -/
def jointMutualInfoBits {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (traceRight rho) + vnEntropy (traceLeft rho) - vnEntropy rho

/-- P.11: the product of the actual marginals, never an unrelated state parameter. -/
def jointMarginalProduct {A B : Type*} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.kronecker (traceRight rho) (traceLeft rho)

/-- P.11: informational distance is the FULL trace norm, without a half factor. -/
def informationalDistance {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  traceNorm (rho - jointMarginalProduct rho)

/-- P.11, Lemma 2.1: exchange the named tensor factors. -/
def swapState {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (B × A) (B × A) ℂ :=
  fun p q => rho (p.2, p.1) (q.2, q.1)

/-- Pp.11–12: probability of a classical A outcome. -/
def classicalWeight {A B : Type*} [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (a : A) : ℝ :=
  (∑ b, rho (a, b) (a, b)).re

/-- Pp.11–12: the normalized conditional B state; the zero-probability branch is set to zero
and is always multiplied by its zero probability in Lemma 3.2. -/
def firstRegisterConditionalBlock {A B : Type*} [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (a : A) : Matrix B B ℂ :=
  fun b b' => (classicalWeight rho a : ℂ)⁻¹ * rho (a, b) (a, b')

/-- P.11, Lemma 3.1: jointly measure a Boolean POVM on A and the standard basis on B. -/
def agreement {A : Type*} [Fintype A]
    (M : Bool → Matrix A A ℂ) (rho : Matrix (A × Bool) (A × Bool) ℂ) : ℝ :=
  ∑ b : Bool, (∑ a, ∑ a', M b a a' * rho (a', b) (a, b)).re

example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (h : rho = jointMarginalProduct rho) :
    informationalDistance rho = 0 := by
  unfold informationalDistance
  rw [sub_eq_zero.mpr h]
  simp [traceNorm, cfc_zero]

example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) :
    swapState (swapState rho) = rho := rfl

example {A B : Type*} [Fintype B] (rho : Matrix (A × B) (A × B) ℂ)
    (a : A) (h : classicalWeight rho a = 0) : firstRegisterConditionalBlock rho a = 0 := by
  ext b b'
  simp [firstRegisterConditionalBlock, h]

example (h : IsDensityMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    relativeEntropyBits (I := Fin 1) 1 1 = 0 := by
  simp [relativeEntropyBits, h, QuantumLoss.umegakiEntropy, cfc_one]

/-- Definition 11, PDF p.12: unrestricted two-sided functional graph.
Both input tables have n entries, each in Fin n; the two copies are separately owned. -/
abbrev PointerMap (n : ℕ) := Fin n → Fin n

/-- The disjoint labelled vertex sets, with standard labels 0,...,n-1 and n,...,2n-1. -/
abbrev Vertex (n : ℕ) := Sum (Fin n) (Fin n)

/-- Definition 11, PDF p.12: no injectivity or acyclicity promise. -/
def successor {n : ℕ} (a b : PointerMap n) : Vertex n → Vertex n
  | .inl v => .inr (a v)
  | .inr v => .inl (b v)

/-- Definition 11, PDF p.12: the endpoint follows k+1 pointers from the fixed Alice vertex. -/
def endpoint {n : ℕ} (k : ℕ) (v1 : Fin n) (a b : PointerMap n) : Vertex n :=
  (successor a b)^[k + 1] (.inl v1)

/-- Definition 11, PDF p.12: standard binary code of the disjoint vertex labels. -/
def vertexLabel {n : ℕ} : Vertex n → ℕ
  | .inl v => v.val
  | .inr v => n + v.val

/-- Definition 11, PDF p.12: XOR of ALL binary bits, independent of leading zero padding. -/
def pointerParity {n : ℕ} (k : ℕ) (v1 : Fin n) (a b : PointerMap n) : Bool :=
  decide ((Nat.digits 2 (vertexLabel (endpoint k v1 a b))).sum % 2 = 1)

/-- Section 6, PDF p.19: the source's DISJ accepts intersecting sets. -/
def nonDisjoint {n : ℕ} (x y : Fin n → Bool) : Bool :=
  decide (∃ i, x i = true ∧ y i = true)

example {n : ℕ} (v : Fin n) (a b : PointerMap n) :
    endpoint 0 v a b = .inr (a v) := rfl

example {n : ℕ} (a b : PointerMap n) (v : Fin n) :
    successor a b (.inr v) = .inl (b v) := rfl

example : nonDisjoint (n := 0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) = false := by
  simp [nonDisjoint]

/-- P.13: saturated real iterated binary logarithm; the zeroth iterate is n. -/
def iteratedLog : ℕ → ℝ → ℝ
  | 0, n => max 1 n
  | j + 1, n => max 1 (Real.logb 2 (iteratedLog j n))

/-- P.13: least iteration reaching one. For positive finite integer n this set is nonempty;
all resource statements exclude n<2. -/
def logStar (n : ℕ) : ℕ := sInf {j : ℕ | iteratedLog j n ≤ 1}

example : iteratedLog 0 1 = 1 := by norm_num [iteratedLog]

/-! Classical protocols: finite public mixtures of finite binary communication trees.
Each bit is selected using only its speaker's input and the public transcript. A change
of speaker starts a new message. An initial empty message is charged as a round.
-/

/-- Definition 4, pp.5–6: a finite deterministic binary protocol with local output. -/
inductive ClassicalTree (X Y O : Type) where
  | outputAlice (f : X → O)
  | outputBob (f : Y → O)
  | alice (bit : X → Bool) (zero one : ClassicalTree X Y O)
  | bob (bit : Y → Bool) (zero one : ClassicalTree X Y O)

/-- Definition 4, pp.5–6: execution follows the local input at each transcript node. -/
def ClassicalTree.run {X Y O : Type} : ClassicalTree X Y O → X → Y → O
  | .outputAlice f, x, _ => f x
  | .outputBob f, _, y => f y
  | .alice bit zero one, x, y => if bit x then one.run x y else zero.run x y
  | .bob bit zero one, x, y => if bit y then one.run x y else zero.run x y

/-- Definition 4, pp.5–6: worst-case transmitted bits; local announcements cost nothing.
Unused branches can be pruned, so this presents every finite worst-case protocol. -/
def ClassicalTree.cost {X Y O : Type} : ClassicalTree X Y O → ℕ
  | .outputAlice _ => 0
  | .outputBob _ => 0
  | .alice _ zero one => 1 + max zero.cost one.cost
  | .bob _ zero one => 1 + max zero.cost one.cost

/-- P.6: number of subsequent speaker changes along the worst branch. -/
def ClassicalTree.changes {X Y O : Type} : ClassicalTree X Y O → Party → ℕ
  | .outputAlice _, _ => 0
  | .outputBob _, _ => 0
  | .alice _ zero one, prev => (if prev = .alice then 0 else 1) +
      max (zero.changes .alice) (one.changes .alice)
  | .bob _ zero one, prev => (if prev = .bob then 0 else 1) +
      max (zero.changes .bob) (one.changes .bob)

/-- P.6: at most k messages with the specified starter, allowing empty padding. -/
def ClassicalTree.rounds {X Y O : Type} (T : ClassicalTree X Y O) (start : Party) : ℕ :=
  match T with
  | .outputAlice _ => 0
  | .outputBob _ => 0
  | .alice _ zero one => (if start = .alice then 1 else 2) +
      max (zero.changes .alice) (one.changes .alice)
  | .bob _ zero one => (if start = .bob then 1 else 2) +
      max (zero.changes .bob) (one.changes .bob)

/-- Definition 4: the public randomness is independent of both inputs. Finite input/cost
protocols have only finitely many distinct deterministic trees, so grouping seeds loses nothing. -/
structure PublicProtocol (X Y O : Type) where
  seeds : ℕ
  weight : Fin seeds → ℝ
  nonnegative : ∀ s, 0 ≤ weight s
  normalized : ∑ s, weight s = 1
  tree : Fin seeds → ClassicalTree X Y O

/-- Definition 4: worst-case communication and rounds on every public seed of positive weight. -/
def PublicProtocol.bounded {X Y O : Type} (P : PublicProtocol X Y O)
    (start : Party) (k c : ℕ) : Prop :=
  ∀ s, 0 < P.weight s → (P.tree s).rounds start ≤ k ∧ (P.tree s).cost ≤ c

/-- Definition 4: correctness for EVERY input, with the protocol fixed before the input. -/
def PublicProtocol.computes {X Y O : Type} [DecidableEq O]
    (P : PublicProtocol X Y O) (f : X → Y → O) (eps : ℝ) : Prop :=
  ∀ x y, 1 - eps ≤ ∑ s, P.weight s * (if (P.tree s).run x y = f x y then 1 else 0)

example {X Y O : Type} (f : X → O) :
    (ClassicalTree.outputAlice (Y := Y) f).cost = 0 := rfl

example {X Y O : Type} (f : Y → O) (x : X) (y : Y) :
    (ClassicalTree.outputBob (X := X) f).run x y = f y := rfl

example (f : Unit → Bool) :
    (ClassicalTree.alice (Y := Unit) (fun _ : Unit => false)
      (.outputAlice f) (.outputAlice f)).rounds .bob = 2 := rfl

/-! Quantum protocols: fixed finite wire ownership, input-local unitaries, fixed transfers,
and a final local POVM. Prior assistance is a single normalized input-independent vector.
-/

/-- Definition 5, p.6: one round's fixed speaker/wires and local-input-controlled unitaries. -/
structure QuantumRound (X Y : Type) (N : ℕ) where
  speaker : Party
  sent : Finset (Fin N)
  alice : X → Matrix.unitaryGroup (Qubits N) ℂ
  bob : Y → Matrix.unitaryGroup (Qubits N) ℂ

/-- Definition 5: the unitary can inspect only its speaker's classical input. -/
def QuantumRound.matrix {X Y : Type} {N : ℕ} (r : QuantumRound X Y N)
    (x : X) (y : Y) : Matrix (Qubits N) (Qubits N) ℂ :=
  if r.speaker = .alice then r.alice x else r.bob y

/-- Definition 5: transferring a fixed set of owned wires changes ownership, not the state. -/
def QuantumRound.update {X Y : Type} {N : ℕ} (r : QuantumRound X Y N)
    (own : Fin N → Party) : Fin N → Party :=
  fun q => if q ∈ r.sent then r.speaker.other else own q

/-- Owned wire set, used to enforce physical locality, p.6. -/
def owned {N : ℕ} (own : Fin N → Party) (p : Party) : Finset (Fin N) :=
  Finset.univ.filter fun q => own q = p

/-- Definition 5: all operations and transfers act only on the speaker's owned wires. -/
def roundsLegal {X Y : Type} {N : ℕ} :
    (Fin N → Party) → List (QuantumRound X Y N) → Prop
  | _, [] => True
  | own, r :: rs => (∀ q ∈ r.sent, own q = r.speaker) ∧
      (∀ x y, ActsWithin (owned own r.speaker) (r.matrix x y)) ∧
      roundsLegal (r.update own) rs

/-- Alternating messages, p.6; t is zero-based. -/
def speakerAt (start : Party) (t : ℕ) : Party :=
  if t % 2 = 0 then start else start.other

/-- Definition 5 and Definition 6, pp.6–7: arbitrary finite private and shared workspace.
Final announcements are a local measurement and are not charged transmissions. -/
structure QuantumProtocol (X Y O : Type) where
  N : ℕ
  initial : EuclideanSpace ℂ (Qubits N)
  owner : Fin N → Party
  rounds : List (QuantumRound X Y N)
  outputParty : Party
  measureAlice : X → O → Matrix (Qubits N) (Qubits N) ℂ
  measureBob : Y → O → Matrix (Qubits N) (Qubits N) ℂ

/-- Ownership at the cut after t messages (before message t+1), pp.14–15. -/
def QuantumProtocol.ownerAt {X Y O : Type} (P : QuantumProtocol X Y O) (t : ℕ) :
    Fin P.N → Party :=
  (P.rounds.take t).foldl (fun own r => r.update own) P.owner

/-- Input-local final POVM, Definition 5. -/
def QuantumProtocol.measurement {X Y O : Type} (P : QuantumProtocol X Y O)
    (x : X) (y : Y) : O → Matrix (Qubits P.N) (Qubits P.N) ℂ :=
  if P.outputParty = .alice then P.measureAlice x else P.measureBob y

/-- Definition 5: all registers normalized, all transfers legal, exactly k alternating
messages (possibly empty), and a local output POVM. -/
def QuantumProtocol.valid {X Y O : Type} [Fintype O]
    (P : QuantumProtocol X Y O) (start : Party) (k : ℕ) : Prop :=
  ‖P.initial‖ = 1 ∧ P.rounds.length = k ∧ roundsLegal P.owner P.rounds ∧
  (∀ i : Fin P.rounds.length, (P.rounds.get i).speaker = speakerAt start i.val) ∧
  ∀ x y, IsPOVM (P.measurement x y) ∧ ∀ o,
    ActsWithin (owned (P.ownerAt P.rounds.length) P.outputParty) (P.measurement x y o)

/-- Definition 5: structural count of transmitted qubits, never a free cost label. -/
def QuantumProtocol.cost {X Y O : Type} (P : QuantumProtocol X Y O) : ℕ :=
  (P.rounds.map fun r => r.sent.card).sum

/-- Definition 5: actual execution, with all round unitaries fixed before either input. -/
def QuantumProtocol.stateAt {X Y O : Type} (P : QuantumProtocol X Y O)
    (x : X) (y : Y) (t : ℕ) : EuclideanSpace ℂ (Qubits P.N) :=
  (P.rounds.take t).foldl (fun psi r => act (r.matrix x y) psi) P.initial

/-- Definition 5: the final local measurement's output distribution. -/
def QuantumProtocol.probability {X Y O : Type} (P : QuantumProtocol X Y O)
    (x : X) (y : Y) (o : O) : ℝ :=
  effectProb (P.measurement x y o) (pureDensity (P.stateAt x y P.rounds.length))

/-- Definition 5: bounded error is a worst-case, per-input guarantee. -/
def QuantumProtocol.computes {X Y O : Type} (P : QuantumProtocol X Y O)
    (f : X → Y → O) (eps : ℝ) : Prop :=
  ∀ x y, 1 - eps ≤ P.probability x y (f x y)

example {X Y O : Type} (P : QuantumProtocol X Y O) (x : X) (y : Y) :
    P.stateAt x y 0 = P.initial := rfl

example {X Y O : Type} (P : QuantumProtocol X Y O) (h : P.rounds = []) : P.cost = 0 := by
  simp [QuantumProtocol.cost, h]

/-- P.14, coherent execution for Lemma 7: input registers are explicitly retained, and
measurements pinch only actual local computational registers. No remote path access occurs.
Uniform coherent input, tensor the normalized input-independent work state.
For PointerMap n the normalization factor is exactly 1/n^n. -/
def coherentInitial {X Y O : Type} [Fintype X] [Fintype Y]
    (P : QuantumProtocol X Y O) : EuclideanSpace ℂ ((X × Y) × Qubits P.N) :=
  WithLp.toLp 2 fun z =>
    (((Real.sqrt ((Fintype.card X : ℝ) * Fintype.card Y))⁻¹ : ℝ) : ℂ) * P.initial z.2

/-- Pp.6,14: input controls are block diagonal and leave BOTH input registers unchanged. -/
def controlledRound {X Y : Type} [DecidableEq X] [DecidableEq Y] {N : ℕ}
    (r : QuantumRound X Y N) : Matrix ((X × Y) × Qubits N) ((X × Y) × Qubits N) ℂ :=
  fun p q => if p.1 = q.1 then r.matrix p.1.1 p.1.2 p.2 q.2 else 0

/-- Pp.14,18: optional standard-basis measurements of specified physical registers.
The X and Y registers belong to Alice and Bob respectively; each work wire has its current owner. -/
structure MeasurementPattern (N : ℕ) where
  aliceInput : Bool
  bobInput : Bool
  wires : Finset (Fin N)

/-- Pp.14,18: nonselective local measurements, keeping all classical values in their registers.
This is the product of the owners' local dephasings, with no communicated outcome for free. -/
def dephaseSelectedRegisters {X Y : Type} [DecidableEq X] [DecidableEq Y] {N : ℕ}
    (m : MeasurementPattern N)
    (rho : Matrix ((X × Y) × Qubits N) ((X × Y) × Qubits N) ℂ) :
    Matrix ((X × Y) × Qubits N) ((X × Y) × Qubits N) ℂ :=
  fun p q => if (m.aliceInput = false ∨ p.1.1 = q.1.1) ∧
    (m.bobInput = false ∨ p.1.2 = q.1.2) ∧ (∀ w ∈ m.wires, p.2 w = q.2 w)
    then rho p q else 0

/-- Pp.14,18: constructed state after t messages, with any chosen local register measurements
at each cut. The all-empty pattern is the unmeasured run. -/
def coherentExecutionStateAt {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (P : QuantumProtocol X Y O) (m : ℕ → MeasurementPattern P.N) :
    ℕ → Matrix ((X × Y) × Qubits P.N) ((X × Y) × Qubits P.N) ℂ
  | 0 => dephaseSelectedRegisters (m 0) (pureDensity (coherentInitial P))
  | t + 1 => match P.rounds[t]? with
      | none => coherentExecutionStateAt P m t
      | some r => dephaseSelectedRegisters (m (t + 1))
          (controlledRound r * coherentExecutionStateAt P m t * (controlledRound r)ᴴ)

/-- Alice's actual owned work configurations at a cut, pp.14,18. -/
abbrev AliceConfig {N : ℕ} (own : Fin N → Party) := {q : Fin N // own q = .alice} → Bool

/-- Complementary work configurations; with two parties these are exactly Bob's wires. -/
abbrev BobConfig {N : ℕ} (own : Fin N → Party) := {q : Fin N // own q ≠ .alice} → Bool

/-- Recombine local work configurations on the same physical wires. -/
def mergeWork {N : ℕ} (own : Fin N → Party) (a : AliceConfig own) (b : BobConfig own) :
    Qubits N :=
  fun q => if h : own q = .alice then a ⟨q, h⟩ else b ⟨q, h⟩

/-- Lemma 7, p.18: the actual (F_A M_A):F_B reduction, tracing out only Bob's WORK wires.
Input registers remain in the state and are not replaced by arbitrary marginals. -/
def aliceInputJoint {X Y : Type} {N : ℕ} (own : Fin N → Party)
    (rho : Matrix ((X × Y) × Qubits N) ((X × Y) × Qubits N) ℂ) :
    Matrix ((X × AliceConfig own) × Y) ((X × AliceConfig own) × Y) ℂ :=
  fun p q => ∑ b : BobConfig own,
    rho ((p.1.1, p.2), mergeWork own p.1.2 b)
      ((q.1.1, q.2), mergeWork own q.1.2 b)

example {X Y : Type} [DecidableEq X] [DecidableEq Y] {N : ℕ}
    (rho : Matrix ((X × Y) × Qubits N) ((X × Y) × Qubits N) ℂ) :
    dephaseSelectedRegisters ⟨false, false, ∅⟩ rho = rho := by
  ext p q
  simp [dephaseSelectedRegisters]

example {X Y : Type} [DecidableEq X] [DecidableEq Y] {N : ℕ}
    (r : QuantumRound X Y N) (x : X) (y : Y) (z z' : Qubits N) :
    controlledRound r ((x,y),z) ((x,y),z') = r.matrix x y z z' := by
  simp [controlledRound]

/- Lemma 7 is intentionally not asserted. The coherent execution above makes its
prior-entanglement counterexample precise; see this unit's HARD.md and MODERATION_NOTES.md.
A classical input reference would change the printed unmeasured-input claim. -/

/-! Local CPTP protocols, pp.6–7. Private environments may be preallocated to any finite size;
the simulation theorem puts no erroneous dimension bound on the new ancillas.
-/

/-- Definition 2 and the model paragraph p.6: a CPTP operation local to S.
The finite normalized Kraus family gives complete positivity, complex linearity and trace preservation. -/
def LocalChannel {N : ℕ} (S : Finset (Fin N)) (F : Superop (Qubits N) (Qubits N)) : Prop :=
  ∃ (d : ℕ) (E : Fin d → Matrix (Qubits N) (Qubits N) ℂ),
    IsKrausFamily E ∧ (∀ j, ActsWithin S (E j)) ∧ ∀ rho, F rho = krausApply E rho

/-- P.6: a round in the local CPTP model, with fixed sender, transfers and boundaries. -/
structure ChannelRound (X Y : Type) (N : ℕ) where
  speaker : Party
  sent : Finset (Fin N)
  alice : X → Superop (Qubits N) (Qubits N)
  bob : Y → Superop (Qubits N) (Qubits N)

/-- P.6: local classical input control for a general local quantum operation. -/
def ChannelRound.operation {X Y : Type} {N : ℕ} (r : ChannelRound X Y N)
    (x : X) (y : Y) : Superop (Qubits N) (Qubits N) :=
  if r.speaker = .alice then r.alice x else r.bob y

/-- P.6: changing the owner of exactly the specified sent wires. -/
def ChannelRound.update {X Y : Type} {N : ℕ} (r : ChannelRound X Y N)
    (own : Fin N → Party) : Fin N → Party :=
  fun q => if q ∈ r.sent then r.speaker.other else own q

/-- P.6: legality ensures there are no remote operations or undeclared transmissions. -/
def channelRoundsLegal {X Y : Type} {N : ℕ} :
    (Fin N → Party) → List (ChannelRound X Y N) → Prop
  | _, [] => True
  | own, r :: rs => (∀ q ∈ r.sent, own q = r.speaker) ∧
      (∀ x y, LocalChannel (owned own r.speaker) (r.operation x y)) ∧
      channelRoundsLegal (r.update own) rs

/-- P.6: the same fixed communication model with local CPTP maps in place of unitaries. -/
structure ChannelProtocol (X Y O : Type) where
  N : ℕ
  initial : EuclideanSpace ℂ (Qubits N)
  owner : Fin N → Party
  rounds : List (ChannelRound X Y N)
  outputParty : Party
  measureAlice : X → O → Matrix (Qubits N) (Qubits N) ℂ
  measureBob : Y → O → Matrix (Qubits N) (Qubits N) ℂ

/-- P.6: final ownership after all fixed transfers. -/
def ChannelProtocol.finalOwner {X Y O : Type} (P : ChannelProtocol X Y O) : Fin P.N → Party :=
  P.rounds.foldl (fun own r => r.update own) P.owner

/-- P.6: the announcing player's own-input-controlled measurement. -/
def ChannelProtocol.measurement {X Y O : Type} (P : ChannelProtocol X Y O)
    (x : X) (y : Y) : O → Matrix (Qubits P.N) (Qubits P.N) ℂ :=
  if P.outputParty = .alice then P.measureAlice x else P.measureBob y

/-- P.6: complete validity conditions, including normalization and a local output. -/
def ChannelProtocol.valid {X Y O : Type} [Fintype O]
    (P : ChannelProtocol X Y O) (start : Party) (k : ℕ) : Prop :=
  ‖P.initial‖ = 1 ∧ P.rounds.length = k ∧ channelRoundsLegal P.owner P.rounds ∧
  (∀ i : Fin P.rounds.length, (P.rounds.get i).speaker = speakerAt start i.val) ∧
  ∀ x y, IsPOVM (P.measurement x y) ∧ ∀ o,
    ActsWithin (owned P.finalOwner P.outputParty) (P.measurement x y o)

/-- P.6: the actual output density matrix after all local channels and ownership transfers. -/
def ChannelProtocol.finalState {X Y O : Type} (P : ChannelProtocol X Y O)
    (x : X) (y : Y) : Matrix (Qubits P.N) (Qubits P.N) ℂ :=
  P.rounds.foldl (fun rho r => r.operation x y rho) (pureDensity P.initial)

/-- P.6: the structural communication cost. -/
def ChannelProtocol.cost {X Y O : Type} (P : ChannelProtocol X Y O) : ℕ :=
  (P.rounds.map fun r => r.sent.card).sum

/-- P.6: the full measured output law to be preserved by simulation. -/
def ChannelProtocol.probability {X Y O : Type} (P : ChannelProtocol X Y O)
    (x : X) (y : Y) (o : O) : ℝ :=
  effectProb (P.measurement x y o) (P.finalState x y)

/-- P.6: additional PRIVATE blank ancillas, rather than stronger prior entanglement or advice.
The injection preserves the original ownership and embeds exactly the original initial vector. -/
def BlankExtension {X Y O : Type} (P : ChannelProtocol X Y O)
    (Q : QuantumProtocol X Y O) : Prop :=
  ∃ e : Fin P.N ↪ Fin Q.N, (∀ q, Q.owner (e q) = P.owner q) ∧
    ∀ z : Qubits Q.N, Q.initial z =
      if ∀ q, q ∉ Set.range e → z q = false then P.initial (z ∘ e) else 0

example {X Y O : Type} (P : ChannelProtocol X Y O) (h : P.rounds = []) (x : X) (y : Y) :
    P.finalState x y = pureDensity P.initial := by
  simp [ChannelProtocol.finalState, h]

example {X Y O : Type} (P : ChannelProtocol X Y O) (h : P.rounds = []) : P.cost = 0 := by
  simp [ChannelProtocol.cost, h]

/-- P.7: Alice prepares the input-independent shared vector on local wires, then sends
exactly the wires intended for Bob; the preparation phase is uncharged. -/
def preparationRound {N : ℕ} (own : Fin N → Party)
    (U : Matrix.unitaryGroup (Qubits N) ℂ) : QuantumRound Unit Unit N where
  speaker := .alice
  sent := owned own .bob
  alice := fun _ => U
  bob := fun _ => 1

example {N : ℕ} (own : Fin N → Party) (U : Matrix.unitaryGroup (Qubits N) ℂ) :
    (preparationRound own U).sent = owned own .bob := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P81


