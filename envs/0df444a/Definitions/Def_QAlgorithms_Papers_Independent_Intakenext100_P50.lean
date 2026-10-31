-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P50
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P50
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:48:04.170062+00:00
-- url     : https://prove2.me/theorems/98585b73-2061-4253-b29d-528dbb804928
-- title:
--   Definitions for Quantum Feedback Channels
-- statement:
--   The objects the formalized statements of *Quantum Feedback Channels* (arXiv:quant-ph/0209076) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Feedback`: PDF p.1: absent, classical, or unrestricted quantum return communication.
--   - `tensorFirst`: PDF pp.1–2: apply a map on the first register and identity on the second, including its off-diagonal blocks.
--   - `forward`: PDF p.2, Lemma 1: exactly one forward call, with identity on both memories. The input and output ports may have different dimensions.
--   - `returnRegister`: PDF pp.1–2: move Bob's return register F to Alice. Classical feedback dephases F in its distinguished basis; quantum feedback preserves all coherences and correlations. For absent feedback F is one-dimensional, enforced in BowenFeedbackProtocol.Legal.
--   - `BowenFeedbackProtocol`: PDF p.2, §III.A: an n-use causal interaction. Only Alice's maps see the preselected message x. Bob's maps never do. Prelude communication permits resource preparation before the first counted forward use. There is no bound on a, b or f. The external classical message reference is never acted on.
--   - `BowenFeedbackProtocol.Legal`: PDF pp.1–2: every used local operation is CPTP; classical return is dephased by execution, and no feedback has a one-dimensional return register.
--   - `BowenFeedbackProtocol.prelude`: PDF pp.1–2: free local operations and backward communication before use one.
--   - `BowenFeedbackProtocol.step`: PDF p.2, four steps in Lemma 1: encode, apply N once, Bob's processing, return a register, Alice's local processing.
--   - `BowenFeedbackProtocol.run`: PDF pp.2–3: the same memoryless N is used once at each recursive step. Only the first n steps are used by a code.
--   - `BowenFeedbackProtocol.receiver`: PDF p.3, Eqs. (8)–(12): information is in Bob's retained memory, not the joint laboratories. Bob's memory includes all outputs and outcomes he retains.
--   - `InitialResource`: PDF pp.1–2: initial resources are independent of the selected message. Unassisted protocols begin with a product density; assisted protocols may share any density. The prelude can distribute entanglement using quantum feedback.
--   - `BowenClassicalCode`: PDF pp.2–3: a finite classical code with a fixed initial density and a message-independent POVM on Bob's final register.
--   - `BowenClassicalCode.Legal`: PDF pp.1–3: admissibility of the executed classical code.
--   - `BowenClassicalCode.error`: PDF p.3, Theorem 2: the actual average error for uniformly selected block messages. This family satisfies the source's AEP convention.
--   - `BowenClassicalAchievable`: PDF pp.1–3: vanishing-error classical rates, in bits per forward channel use. For each large n one code handles all messages; memories and shared resources may grow with n. Neither an information bound nor the desired converse is assumed.
--   - `bowenClassicalCapacity`: PDF p.1: operational classical capacity. The complete ordered extended-real codomain avoids the empty/unbounded real-supremum default. Zero is included.
--   - `bowenCqInformation`: PDF p.2, Definition 1 and Eqs. (2)–(3): cq mutual information in entropy form, S(sum p_x rho_x) - sum p_x S(rho_x). Used only with normalized densities.
--   - `BowenInputEnsemble`: PDF p.2, Lemma 1: a finite ensemble on input A and arbitrary finite B. The conditional density depends on the message, as the PDF's superscript i requires.
--   - `bowenConditionalInformation`: PDF p.2, Eq. (7), and p.3, Eq. (13): I(M:A_out|B), written as the difference of the two cq Holevo informations. B's marginal is unchanged by N.
--   - `maxConditionalInformation`: PDF pp.2–3: supremal single-use conditional information over every finite message alphabet, normalized prior, conditional density and auxiliary dimension. This is the source's maximum value, with no imposed auxiliary-dimension bound.
--   - `BowenQuantumCode`: PDF p.1: an entanglement-transmission code with k logical qubits. The shared resource is independent of the logical input. The reference in entanglement fidelity is external to the executed protocol, and Bob's maps cannot access it.
--   - `BowenQuantumCode.Legal`: PDF p.1: CPTP quantum encoding and decoding, with the chosen initial resource.
--   - `BowenQuantumCode.start`: PDF p.1: tensor the logical input with an independent shared density, then apply Alice's input encoder while retaining Bob's share untouched.
--   - `BowenQuantumCode.channel`: PDF p.1: the actual end-to-end channel on the k logical qubits, using the same forward N at all n calls and only the permitted return resource.
--   - `QuantumAchievable`: PDF p.1: asymptotic quantum communication with entanglement fidelity tending to one and k/n approaching R from below; rates are qubits per forward use.
--   - `bowenQuantumCapacity`: PDF p.1 and conclusion pp.4–5: operational vanishing-error quantum capacity.
-- source:
--   Quantum Feedback Channels, arXiv:quant-ph/0209076v4, https://arxiv.org/abs/quant-ph/0209076v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Bowen, Quantum Feedback Channels, arXiv:quant-ph/0209076v4.
Paper-local operational definitions: finite memories have arbitrary dimensions, chosen
separately for each code. A single sufficiently large memory holds all retained systems
of a finite protocol; local CPTP maps include ancillas, discarded environments and outcomes.
Capacities and the one-use supremum take values in EReal, avoiding a real-supremum default
on an unbounded set. All entropies and rates use base two.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P50

open QAlgorithms

/-- PDF p.1: absent, classical, or unrestricted quantum return communication. -/
inductive Feedback where
  | none
  | classical
  | quantum
  deriving DecidableEq

/-- PDF pp.1–2: apply a map on the first register and identity on the second,
including its off-diagonal blocks. -/
def tensorFirst {A C B : Type*} (T : Superop A C) : Superop (A × B) (C × B) :=
  fun X p q => T (fun a c => X (a, p.2) (c, q.2)) p.1 q.1

/-- PDF p.2, Lemma 1: exactly one forward call, with identity on both memories.
The input and output ports may have different dimensions. -/
def forward {A B I O : Type*} (N : Superop I O) :
    Superop ((A × I) × B) (A × (O × B)) :=
  fun X p q => N (fun i j => X ((p.1, i), p.2.2) ((q.1, j), q.2.2)) p.2.1 q.2.1

/-- PDF pp.1–2: move Bob's return register F to Alice. Classical feedback dephases F
in its distinguished basis; quantum feedback preserves all coherences and correlations.
For absent feedback F is one-dimensional, enforced in BowenFeedbackProtocol.Legal. -/
def returnRegister {A B F : Type*} [DecidableEq F] (mode : Feedback) :
    Superop (A × (F × B)) ((A × F) × B) :=
  fun X p q => if mode = .classical ∧ p.1.2 ≠ q.1.2 then 0
    else X (p.1.1, (p.1.2, p.2)) (q.1.1, (q.1.2, q.2))

/-- PDF p.2, §III.A: an n-use causal interaction. Only Alice's maps see the
preselected message x. Bob's maps never do. Prelude communication permits resource
preparation before the first counted forward use. There is no bound on a, b or f.
The external classical message reference is never acted on. -/
structure BowenFeedbackProtocol (i o m n : ℕ) where
  a : ℕ
  b : ℕ
  f : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  f_pos : 0 < f
  bobPrelude : Superop (Fin b) (Fin f × Fin b)
  alicePrelude : Fin m → Superop (Fin a × Fin f) (Fin a)
  encode : ℕ → Fin m → Superop (Fin a) (Fin a × Fin i)
  bob : ℕ → Superop (Fin o × Fin b) (Fin f × Fin b)
  alice : ℕ → Fin m → Superop (Fin a × Fin f) (Fin a)

/-- PDF pp.1–2: every used local operation is CPTP; classical return is dephased
by execution, and no feedback has a one-dimensional return register. -/
def BowenFeedbackProtocol.Legal {i o m n : ℕ} (P : BowenFeedbackProtocol i o m n) (mode : Feedback) : Prop :=
  (mode = .none → P.f = 1) ∧ IsChannel P.bobPrelude ∧
  (∀ x, IsChannel (P.alicePrelude x)) ∧
  (∀ k < n, ∀ x, IsChannel (P.encode k x)) ∧
  (∀ k < n, IsChannel (P.bob k)) ∧
  (∀ k < n, ∀ x, IsChannel (P.alice k x))

/-- PDF pp.1–2: free local operations and backward communication before use one. -/
def BowenFeedbackProtocol.initialStage {i o m n : ℕ} (P : BowenFeedbackProtocol i o m n) (mode : Feedback)
    (x : Fin m) : Superop (Fin P.a × Fin P.b) (Fin P.a × Fin P.b) :=
  fun X => tensorFirst (P.alicePrelude x)
    (returnRegister mode (idTensorSuperop P.bobPrelude X))

/-- PDF p.2, four steps in Lemma 1: encode, apply N once, Bob's processing,
return a register, Alice's local processing. -/
def BowenFeedbackProtocol.step {i o m n : ℕ} (P : BowenFeedbackProtocol i o m n) (mode : Feedback)
    (N : Superop (Fin i) (Fin o)) (k : ℕ) (x : Fin m) :
    Superop (Fin P.a × Fin P.b) (Fin P.a × Fin P.b) :=
  fun X => tensorFirst (P.alice k x)
    (returnRegister mode (idTensorSuperop (P.bob k)
      (forward N (tensorFirst (P.encode k x) X))))

/-- PDF pp.2–3: the same memoryless N is used once at each recursive step.
Only the first n steps are used by a code. -/
def BowenFeedbackProtocol.run {i o m n : ℕ} (P : BowenFeedbackProtocol i o m n) (mode : Feedback)
    (N : Superop (Fin i) (Fin o)) (x : Fin m)
    (X : Matrix (Fin P.a × Fin P.b) (Fin P.a × Fin P.b) ℂ) :
    ℕ → Matrix (Fin P.a × Fin P.b) (Fin P.a × Fin P.b) ℂ
  | 0 => P.initialStage mode x X
  | k + 1 => P.step mode N k x (P.run mode N x X k)

/-- PDF p.3, Eqs. (8)–(12): information is in Bob's retained memory, not the
joint laboratories. Bob's memory includes all outputs and outcomes he retains. -/
def BowenFeedbackProtocol.receiver {i o m n : ℕ} (P : BowenFeedbackProtocol i o m n) (mode : Feedback)
    (N : Superop (Fin i) (Fin o)) (x : Fin m)
    (X : Matrix (Fin P.a × Fin P.b) (Fin P.a × Fin P.b) ℂ) :
    Matrix (Fin P.b) (Fin P.b) ℂ :=
  traceLeft (P.run mode N x X n)

/-- PDF pp.1–2: initial resources are independent of the selected message.
Unassisted protocols begin with a product density; assisted protocols may share
any density. The prelude can distribute entanglement using quantum feedback. -/
def InitialResource {A B : Type*} [Fintype A] [Fintype B]
    (assisted : Bool) (X : Matrix (A × B) (A × B) ℂ) : Prop :=
  IsDensityMatrix X ∧ (assisted = true ∨
    ∃ (s : Matrix A A ℂ) (t : Matrix B B ℂ),
      IsDensityMatrix s ∧ IsDensityMatrix t ∧ X = Matrix.kronecker s t)

/-- PDF pp.2–3: a finite classical code with a fixed initial density and a
message-independent POVM on Bob's final register. -/
structure BowenClassicalCode (i o m n : ℕ) where
  messages_pos : 0 < m
  protocol : BowenFeedbackProtocol i o m n
  initial : Matrix (Fin protocol.a × Fin protocol.b) (Fin protocol.a × Fin protocol.b) ℂ
  decode : Fin m → Matrix (Fin protocol.b) (Fin protocol.b) ℂ

/-- PDF pp.1–3: admissibility of the executed classical code. -/
def BowenClassicalCode.Legal {i o m n : ℕ} (C : BowenClassicalCode i o m n)
    (mode : Feedback) (assisted : Bool) : Prop :=
  C.protocol.Legal mode ∧ InitialResource assisted C.initial ∧ IsPOVM C.decode

/-- PDF p.3, Theorem 2: the actual average error for uniformly selected block
messages. This family satisfies the source's AEP convention. -/
def BowenClassicalCode.error {i o m n : ℕ} (C : BowenClassicalCode i o m n)
    (mode : Feedback) (N : Superop (Fin i) (Fin o)) : ℝ :=
  1 - (m : ℝ)⁻¹ * ∑ x : Fin m,
    effectProb (C.decode x) (C.protocol.receiver mode N x C.initial)

/-- PDF pp.1–3: vanishing-error classical rates, in bits per forward channel use.
For each large n one code handles all messages; memories and shared resources
may grow with n. Neither an information bound nor the desired converse is assumed. -/
def BowenClassicalAchievable {i o : ℕ} (N : Superop (Fin i) (Fin o))
    (mode : Feedback) (assisted : Bool) (R : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ m : ℕ, ∃ C : BowenClassicalCode i o m n,
      C.Legal mode assisted ∧ (R - delta) * n ≤ Real.logb 2 m ∧
      C.error mode N ≤ eps

/-- PDF p.1: operational classical capacity. The complete ordered extended-real
codomain avoids the empty/unbounded real-supremum default. Zero is included. -/
def bowenClassicalCapacity {i o : ℕ} (N : Superop (Fin i) (Fin o))
    (mode : Feedback) (assisted : Bool) : EReal :=
  sSup {v | v = 0 ∨ ∃ R : ℝ, 0 ≤ R ∧ v = (R : EReal) ∧
    BowenClassicalAchievable N mode assisted R}

/-- PDF p.2, Definition 1 and Eqs. (2)–(3): cq mutual information in entropy
form, S(sum p_x rho_x) - sum p_x S(rho_x). Used only with normalized densities. -/
def bowenCqInformation {d m : ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  vnEntropy (∑ x, (p x : ℂ) • rho x) - ∑ x, p x * vnEntropy (rho x)

/-- PDF p.2, Lemma 1: a finite ensemble on input A and arbitrary finite B.
The conditional density depends on the message, as the PDF's superscript i requires. -/
structure BowenInputEnsemble (i : ℕ) where
  m : ℕ
  b : ℕ
  m_pos : 0 < m
  b_pos : 0 < b
  prior : Fin m → ℝ
  prior_nonneg : ∀ x, 0 ≤ prior x
  prior_sum : ∑ x, prior x = 1
  rho : Fin m → Matrix (Fin i × Fin b) (Fin i × Fin b) ℂ
  density : ∀ x, IsDensityMatrix (rho x)

/-- PDF p.2, Eq. (7), and p.3, Eq. (13): I(M:A_out|B), written as the
difference of the two cq Holevo informations. B's marginal is unchanged by N. -/
def bowenConditionalInformation {i o : ℕ} (N : Superop (Fin i) (Fin o))
    (E : BowenInputEnsemble i) : ℝ :=
  (vnEntropy (∑ x, (E.prior x : ℂ) • tensorFirst N (E.rho x)) -
    ∑ x, E.prior x * vnEntropy (tensorFirst N (E.rho x))) -
  bowenCqInformation E.prior (fun x => traceLeft (E.rho x))

/-- PDF pp.2–3: supremal single-use conditional information over every finite
message alphabet, normalized prior, conditional density and auxiliary dimension.
This is the source's maximum value, with no imposed auxiliary-dimension bound. -/
def maxConditionalInformation {i o : ℕ} (N : Superop (Fin i) (Fin o)) : EReal :=
  sSup {v | ∃ E : BowenInputEnsemble i, v = (bowenConditionalInformation N E : EReal)}

/-- PDF p.1: an entanglement-transmission code with k logical qubits. The shared
resource is independent of the logical input. The reference in entanglement fidelity
is external to the executed protocol, and Bob's maps cannot access it. -/
structure BowenQuantumCode (i o n : ℕ) where
  k : ℕ
  a0 : ℕ
  a0_pos : 0 < a0
  protocol : BowenFeedbackProtocol i o 1 n
  resource : Matrix (Fin a0 × Fin protocol.b) (Fin a0 × Fin protocol.b) ℂ
  encodeInput : Superop (Qubits k × Fin a0) (Fin protocol.a)
  decode : Superop (Fin protocol.b) (Qubits k)

/-- PDF p.1: CPTP quantum encoding and decoding, with the chosen initial resource. -/
def BowenQuantumCode.Legal {i o n : ℕ} (C : BowenQuantumCode i o n)
    (mode : Feedback) (assisted : Bool) : Prop :=
  C.protocol.Legal mode ∧ InitialResource assisted C.resource ∧
    IsChannel C.encodeInput ∧ IsChannel C.decode

/-- PDF p.1: tensor the logical input with an independent shared density, then
apply Alice's input encoder while retaining Bob's share untouched. -/
def BowenQuantumCode.start {i o n : ℕ} (C : BowenQuantumCode i o n)
    (X : Matrix (Qubits C.k) (Qubits C.k) ℂ) :
    Matrix (Fin C.protocol.a × Fin C.protocol.b) (Fin C.protocol.a × Fin C.protocol.b) ℂ :=
  tensorFirst C.encodeInput (fun p q =>
    X p.1.1 q.1.1 * C.resource (p.1.2, p.2) (q.1.2, q.2))

/-- PDF p.1: the actual end-to-end channel on the k logical qubits, using the
same forward N at all n calls and only the permitted return resource. -/
def BowenQuantumCode.channel {i o n : ℕ} (C : BowenQuantumCode i o n)
    (mode : Feedback) (N : Superop (Fin i) (Fin o)) : Superop (Qubits C.k) (Qubits C.k) :=
  fun X => C.decode (C.protocol.receiver mode N 0 (C.start X))

/-- PDF p.1: asymptotic quantum communication with entanglement fidelity tending
to one and k/n approaching R from below; rates are qubits per forward use. -/
def QuantumAchievable {i o : ℕ} (N : Superop (Fin i) (Fin o))
    (mode : Feedback) (assisted : Bool) (R : ℝ) : Prop :=
  ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧
    ∀ n ≥ n0, ∃ C : BowenQuantumCode i o n,
      C.Legal mode assisted ∧ (R - delta) * n ≤ C.k ∧
      1 - eps ≤ entanglementFidelity (C.channel mode N)

/-- PDF p.1 and conclusion pp.4–5: operational vanishing-error quantum capacity. -/
def bowenQuantumCapacity {i o : ℕ} (N : Superop (Fin i) (Fin o))
    (mode : Feedback) (assisted : Bool) : EReal :=
  sSup {v | v = 0 ∨ ∃ R : ℝ, 0 ≤ R ∧ v = (R : EReal) ∧
    QuantumAchievable N mode assisted R}

/-! Sanity checks for local definitions; no headline theorem is proved here. -/

example {A B : Type*} (X : Matrix (A × B) (A × B) ℂ) :
    tensorFirst (fun Y : Matrix A A ℂ => Y) X = X := by
  rfl

example {A B I O : Type*} (N : Superop I O)
    (X : Matrix ((A × I) × B) ((A × I) × B) ℂ)
    (p q : A × (O × B)) :
    forward N X p q =
      N (fun i j => X ((p.1, i), p.2.2) ((q.1, j), q.2.2)) p.2.1 q.2.1 := by
  rfl

example {A B F : Type*} [DecidableEq F]
    (X : Matrix (A × (F × B)) (A × (F × B)) ℂ)
    (p q : (A × F) × B) (h : p.1.2 ≠ q.1.2) :
    returnRegister .classical X p q = 0 := by
  simp [returnRegister, h]

example {i o m n : ℕ} (P : BowenFeedbackProtocol i o m n) (mode : Feedback)
    (N : Superop (Fin i) (Fin o)) (x : Fin m)
    (X : Matrix (Fin P.a × Fin P.b) (Fin P.a × Fin P.b) ℂ) :
    P.run mode N x X 0 = P.initialStage mode x X := by
  rfl

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) :
    bowenCqInformation (fun _ : Fin 1 => 1) (fun _ => rho) = 0 := by
  simp [bowenCqInformation]

example {i o n : ℕ} (C : BowenQuantumCode i o n) (mode : Feedback)
    (N : Superop (Fin i) (Fin o)) (X : Matrix (Qubits C.k) (Qubits C.k) ℂ) :
    C.channel mode N X = C.decode (traceLeft
      (C.protocol.run mode N 0 (C.start X) n)) := by
  rfl

end QAlgorithms.Papers.Independent.Intakenext100.P50


