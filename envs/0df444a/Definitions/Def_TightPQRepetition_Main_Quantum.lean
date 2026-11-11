-- Prove2me | Definitions.Def_TightPQRepetition_Main_Quantum
-- name    : TightPQRepetition_Main_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:34:36.657539+00:00
-- url     : https://prove2.me/theorems/60a19fc3-9719-46d3-bc74-ec80074c4fb6
-- title:
--   Quantum provers with quantum advice and quantum distinguishers
-- statement:
--   Quantum circuits are lists of unitary gates on at most two qubits. A **strategy** at one security parameter is a prover: it holds $n$ qubits in an arbitrary pure advice state, and a classical random tape. In round $j$ a classical controller computes a message from what it has seen; the message is written into the core by bit flips on designated wires; a circuit is applied; designated wires are measured in the computational basis; and the controller computes the answer. The state of the core persists from round to round. Applied to a run with measurement outcomes $c_0,c_1,\dots$, the operators give a subnormalized vector whose squared norm is the probability of these outcomes.
--
--   A **QPT prover** is a family of strategies of polynomial size with polynomial-size controllers and one polynomial bound in the security parameter on all controller output lengths. The size counts every round instruction, even an empty step. Thus polynomially many protocol rounds have polynomial total work and communication; polynomial work merely in an exponentially growing view length does not suffice. A **quantum distinguisher** is a polynomial-size circuit with quantum advice and one output qubit. Two families of samplers are **computationally indistinguishable** if every such distinguisher has negligible advantage on their samples.
--
--   The role of the model is that nothing about the prover is assumed beyond polynomial size: it may keep its state entangled across rounds and across all repeated coordinates.
--
--   **Formalization Note** Non-unitary and mixed provers are purified at polynomial cost (PDF p. 22). The numbers of wires loaded and measured in a round are fixed by the wire lists of the core; the classical controller's outputs may vary in length.
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, §3 and proof of Theorem 5.1, printed pp. 6–7, 20 / PDF pp. 8–9, 22

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Complexity

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, §3 and proof of Theorem 5.1
(PDF pp. 8–9, 22): quantum circuits with quantum advice, the provers they define, and quantum
distinguishers.

A prover at one security parameter is a `Strategy`: a quantum core on `n` qubits, starting in an
arbitrary pure advice state (quantum advice), together with a classical controller. In round `j`
the controller turns what it has seen into a classical message, which is written into the core
by bit flips on the wires `inW`; the core applies the unitary of a circuit of one- and two-qubit
gates; the wires `outW` are measured in the computational basis. The state of the core is carried
from round to round, so the core may be entangled with anything it was given. Mixed advice and
non-unitary steps are purified at polynomial cost (PDF p. 22).
-/

open QAlgorithms

/-- The gate set: all unitaries on at most two qubits. The source fixes no gate set; Theorem 3.9
needs exact single-qubit rotations, so the rotation angles are not restricted. -/
def smallGates : Set Gate := {g | g.arity ≤ 2 ∧ g.IsUnitary}

/-- Quantum circuits on `n` wires. -/
abbrev QCircuit (n : ℕ) := Circuit smallGates n

/-- The wires that `x` flips: `w i` is flipped iff bit `i` of `x` is set. Bits of `x` beyond `w`,
or wires of `w` beyond `x`, have no effect. -/
def flipMask {n : ℕ} (w : List (Fin n)) (x : Bits) : Qubits n :=
  fun a => (w.zip x).any (fun p => decide (p.1 = a) && p.2)

/-- Writing the classical string `x` into the wires `w`: the product of the `X` gates selected by
`x`, a permutation of the computational basis. -/
def loadX {n : ℕ} (w : List (Fin n)) (x : Bits) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => if y = (fun a => xor (z a) (flipMask w x a)) then 1 else 0

/-- The projector of the computational-basis measurement of the wires `w` with outcome `c`. -/
def outcomeProj {n : ℕ} (w : List (Fin n)) (c : Bits) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun y => if w.map y = c then 1 else 0

/-- One round of a quantum core. -/
structure RoundStep (n : ℕ) where
  /-- The wires the incoming classical message is written into. -/
  inW : List (Fin n)
  /-- The circuit applied in this round. -/
  circ : QCircuit n
  /-- The wires measured to produce the outgoing classical message. -/
  outW : List (Fin n)

instance {n : ℕ} : Inhabited (RoundStep n) := ⟨⟨[], [], []⟩⟩

/-- The unitary of a round once the message `x` has been written. -/
noncomputable def RoundStep.op {n : ℕ} (s : RoundStep n) (x : Bits) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  s.circ.unitary * loadX s.inW x

/-- A prover at one fixed security parameter. -/
structure Strategy where
  /-- The number of qubits of the quantum core. -/
  n : ℕ
  /-- The initial pure state: the quantum advice. -/
  init : EuclideanSpace ℂ (Qubits n)
  /-- The rounds of the core. A round beyond this list leaves the core alone and measures nothing;
  the controller still answers. -/
  steps : List (RoundStep n)
  /-- The length of the classical random tape. -/
  tape : ℕ
  /-- Round `j` of the controller: from `pack (u :: q₀ :: c₀ :: ⋯ :: q_j)`, with `u` the tape,
  `q_i` the incoming messages and `c_i` the measured core answers, the message for the core. -/
  toCore : ℕ → Bits → Bits
  /-- Round `j` of the controller: from `pack (u :: q₀ :: c₀ :: ⋯ :: q_j :: c_j)`, the outgoing
  answer. -/
  toVerifier : ℕ → Bits → Bits

/-- The round `j` of a strategy. -/
def Strategy.stepAt (S : Strategy) (j : ℕ) : RoundStep S.n := S.steps.getD j default

/-- The number of wires measured in round `j`. -/
def Strategy.outLen (S : Strategy) (j : ℕ) : ℕ := (S.stepAt j).outW.length

/-- A legitimate strategy: a unit advice vector and repetition-free wire lists. -/
def Strategy.Valid (S : Strategy) : Prop :=
  IsState S.init ∧ ∀ s ∈ S.steps, s.inW.Nodup ∧ s.outW.Nodup

/-- Size of a strategy: qubits, tape, explicit round instructions, gates and wires. -/
def Strategy.size (S : Strategy) : ℕ :=
  S.n + S.tape + S.steps.length + (S.steps.map fun s => s.inW.length + s.circ.size + s.outW.length).sum

/-- A QPT prover (PDF pp. 8–9): a family of valid strategies of polynomial size, with quantum
advice and polynomial-size classical controllers whose outputs have a polynomial bound in the
security parameter. The output bound prevents polynomially many rounds from doubling the history
at every round and doing exponential total work despite polynomial cost per input bit. -/
def IsQPT (A : ℕ → Strategy) : Prop :=
  (∀ lam, (A lam).Valid) ∧ PolyBound (fun lam => (A lam).size) ∧
    Efficient₂ (fun lam j => (A lam).toCore j) ∧ Efficient₂ (fun lam j => (A lam).toVerifier j) ∧
    ∃ L : ℕ → ℕ, PolyBound L ∧ ∀ lam j v,
      ((A lam).toCore j v).length ≤ L lam ∧ ((A lam).toVerifier j v).length ≤ L lam

/-- In round `j` the answers of `S` have length `a j`, whatever it has seen: `S` is what a circuit
with a fixed set of output wires computes. This is the form a homomorphic evaluation needs. -/
def Strategy.HasAnswerLen (S : Strategy) (a : ℕ → ℕ) : Prop :=
  ∀ j v, (S.toVerifier j v).length = a j

/-- A classical prover: no quantum core at all, only a randomized classical controller. -/
def Strategy.IsClassical (S : Strategy) : Prop := S.n = 0

/-- The controller's view from the tape and the `(message, core answer)` pairs so far. -/
def controllerView (u : Bits) (hist : List (Bits × Bits)) : List Bits := u :: flattenPairs hist

/-- The classical and quantum state of a run after some rounds. -/
structure RunState (n : ℕ) where
  /-- The subnormalized state of the core; its squared norm is the outcome probability. -/
  ket : EuclideanSpace ℂ (Qubits n)
  /-- The `(message, core answer)` pairs so far. -/
  hist : List (Bits × Bits)
  /-- The answers sent so far. -/
  answers : List Bits

/-- One round: the verifier's message for the answers so far is `query j answers`, and the
measurement of the core has outcome `c`. -/
noncomputable def Strategy.runStep (S : Strategy) (query : ℕ → List Bits → Bits) (u : Bits)
    (st : RunState S.n) (c : Bits) : RunState S.n :=
  let j := st.hist.length
  let q := query j st.answers
  let x := S.toCore j (pack (controllerView u st.hist ++ [q]))
  let s := S.stepAt j
  let hist' := st.hist ++ [(q, c)]
  { ket := act (outcomeProj s.outW c * s.op x) st.ket
    hist := hist'
    answers := st.answers ++ [S.toVerifier j (pack (controllerView u hist'))] }

/-- The run with core outcomes `cs`, from the advice state. -/
noncomputable def Strategy.run (S : Strategy) (query : ℕ → List Bits → Bits) (u : Bits)
    (cs : List Bits) : RunState S.n :=
  cs.foldl (S.runStep query u) ⟨S.init, [], []⟩

/-- All outcomes of the core measurements over `m` rounds. -/
abbrev Strategy.Outcomes (S : Strategy) (m : ℕ) := (j : Fin m) → Qubits (S.outLen j)

/-- An outcome sequence as a list of strings. -/
def Strategy.outcomeList (S : Strategy) {m : ℕ} (f : S.Outcomes m) : List Bits :=
  List.ofFn fun j => toBits (f j)

/-- A quantum distinguisher at one security parameter, with quantum advice: on classical input
`x` it writes `x` into `inW`, applies `circ`, and outputs the measured value of `out`. -/
structure QTest where
  /-- Number of qubits. -/
  n : ℕ
  /-- The quantum advice. -/
  advice : EuclideanSpace ℂ (Qubits n)
  /-- The input wires. -/
  inW : List (Fin n)
  /-- The circuit. -/
  circ : QCircuit n
  /-- The measured output wire. -/
  out : List (Fin n)

/-- Size of a distinguisher. -/
def QTest.size (T : QTest) : ℕ := T.n + T.inW.length + T.circ.size

/-- The probability that the distinguisher outputs `1` on the input `x`. -/
noncomputable def QTest.accept (T : QTest) (x : Bits) : ℝ :=
  ‖act (outcomeProj T.out [true] * T.circ.unitary * loadX T.inW x) T.advice‖ ^ 2

/-- A non-uniform polynomial-size quantum distinguisher with quantum advice. -/
def IsQTestFamily (T : ℕ → QTest) : Prop :=
  (∀ lam, IsState (T lam).advice ∧ (T lam).inW.Nodup ∧ (T lam).out.length = 1) ∧
    PolyBound (fun lam => (T lam).size)

/-- The expectation over uniform coins of length `c`. -/
noncomputable def avgCoins (c : ℕ) (g : Bits → ℝ) : ℝ :=
  ((2 : ℝ) ^ c)⁻¹ * ∑ r : Qubits c, g (toBits r)

/-- Computational indistinguishability of two families of samplers, to polynomial-size quantum
adversaries with quantum advice: `D b lam` maps `c b lam` uniform coins to a sample. -/
def CompIndist (c0 c1 : ℕ → ℕ) (D0 D1 : ℕ → Bits → Bits) : Prop :=
  ∀ T : ℕ → QTest, IsQTestFamily T →
    Negligible fun lam =>
      |avgCoins (c0 lam) (fun r => (T lam).accept (D0 lam r)) -
        avgCoins (c1 lam) (fun r => (T lam).accept (D1 lam r))|

end TightPQRepetition.Main


