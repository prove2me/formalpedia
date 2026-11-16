-- Prove2me | Definitions.Def_SYKLearn_Supplement_EvolutionLearner
-- name    : SYKLearn_Supplement_EvolutionLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:36:37.732199+00:00
-- url     : https://prove2.me/theorems/e4cbaa7b-3ed7-48cb-aa00-9bf267e9f4a4
-- title:
--   Adaptive learners with oracle access to a fixed unknown unitary (calls to $U$ counted apart from gates)
-- statement:
--   An **evolution learner** is an adaptive quantum algorithm that has black-box access to an unknown unitary $U$ on $w$ qubits and outputs a string of bits. It runs in rounds $k=1,\dots,R$.
--
--   1. Round $k$ uses $w+a_k$ qubits, all prepared in $|0\rangle$. Its template is a list of steps; each step is either a gate from $\{H,T,\mathrm{CNOT}\}$ on distinct qubits, or one **call to the oracle**, which applies $U$ to the first $w$ qubits and the identity to the $a_k$ ancillas.
--   2. Each step may be switched on or off by a classical bit that a Boolean circuit computes from the measurement outcomes of the earlier rounds. The oracle is only ever applied as $U$: never coherently controlled, inverted, or at another evolution time.
--   3. At the end of the round every qubit is measured in the computational basis; if $V_k$ is the product of the switched-on steps, outcome $z$ has probability $|\langle z|V_k|0\cdots0\rangle|^2$.
--   4. A final Boolean circuit maps the record of all outcomes to the output bits.
--
--   The **number of queries** is the total number of oracle steps in all templates (a worst-case count, whether or not a step is switched on). The **time** is the number of gate steps, plus the number of ancillas, plus the number of Boolean gates; it excludes the oracle calls. The probability that the output satisfies a property $E$ is the sum over all outcome records of the chain-rule probability of the record times the indicator of $E$ at the output.
--
--   This is the model in which Theorem 1.2 counts applications of $U_\star=e^{-\iota t_\star H_g}$ separately from "the gate and classical processing costs, excluding the calls to $U_\star$". Randomized state preparation, such as the random Pauli eigenstates of §5.2, is obtained by measuring ancillas.
--
--   **Formalization Note** The structure copies the published copy-learner `StationarityTest.GibbsLearner` (same gate set, same classical control by Boolean circuits, same output circuit and the same time count), with copies of an unknown state replaced by calls to an unknown unitary. The output bits are read by the published decoder `StationarityTest.decodeBlocks`.
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), §5 opening paragraph, p.43; §5.2, pp.44–45; Theorem 1.2, p.3

import Mathlib
import Definitions.Def_StationarityTest_Learner

noncomputable section
open Matrix QAlgorithms

namespace SYKLearn.Supplement

/-!
# Adaptive learners with oracle access to a fixed unknown unitary

A. Anshu, S. Arunachalam, S. Chen, Y. Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission (held file sha256 5d7d199a…), §5 opening paragraph, p.43; §5.2, pp.44–45. The paper
names no model of computation for Theorem 1.2 ("an algorithm making `N` applications of the
unitary `U⋆` … the gate and classical processing costs, excluding the calls to `U⋆`"); this is the
model of the published `StationarityTest.GibbsLearner`, with the copies of an unknown state
replaced by calls to an unknown unitary.

**Formalization Note.**
* A learner proceeds in rounds `k < R`. Round `k` acts on `w + anc k` wires, all prepared in `|0⟩`
  (there is no unknown input state). The unknown unitary `U` acts on `w` qubits. The round runs a
  list of steps; each step is either a gate of the published gate set `{H, T, CNOT}`
  (`QAlgorithms.htcxGateSet`) on distinct wires, or one **call to the oracle**, which applies `U`
  to wires `0, …, w − 1` and the identity to the other wires. Each step is optionally switched on
  or off by a control bit that a Boolean circuit computes from the outcomes of the earlier rounds
  (classical control only: the oracle is never applied coherently controlled, inverted, or for any
  other time). At the end of the round every wire is measured in the computational basis.
* The law of the outcome record is the chain rule of the Born probabilities `|⟨z|V|0⋯0⟩|²`, where
  `V` is the product of the switched-on steps of the round (first step rightmost). Randomness
  (e.g. random Pauli eigenstates, p.45) comes from measuring ancillas, in the same or earlier
  rounds. A final Boolean circuit maps the record to the output bits, which are read by the
  published decoder `StationarityTest.decodeBlocks`.
* `queriesUsed` is the total number of oracle steps in all round templates, counted whether or not
  a step is switched on (a worst-case count). `time` counts gate steps, ancilla wires and Boolean
  gates, exactly as `StationarityTest.GibbsLearner.time`, and excludes the oracle steps, as the
  paper's "gate and classical processing costs, excluding the calls to `U⋆`" does.
* The learner is data fixed before the unknown unitary.
-/

/-- One step of a round on `w + a` wires: a gate application over `{H, T, CNOT}`, or one call to the
unknown `w`-qubit unitary on wires `0, …, w − 1`. -/
inductive EvolStep (w a : ℕ) where
  /-- A gate of `{H, T, CNOT}` on distinct wires. -/
  | gate (g : GateApp htcxGateSet (w + a))
  /-- One application of the unknown unitary to wires `0, …, w − 1`. -/
  | oracle

namespace EvolStep

variable {w a : ℕ}

/-- The matrix a step applies when the unknown unitary is `U`: the gate tensored with the identity,
or `U` on wires `0, …, w − 1` tensored with the identity on the `a` other wires. -/
def mat (U : Matrix (Qubits w) (Qubits w) ℂ) : EvolStep w a → Matrix (Qubits (w + a)) (Qubits (w + a)) ℂ
  | gate g => embedOp g.gate.mat g.wires
  | oracle => embedOp U (Fin.castAddEmb a)

/-- Whether a step is an oracle call. -/
def isOracle : EvolStep w a → Bool
  | gate _ => false
  | oracle => true

end EvolStep

/-- An adaptive learner with oracle access to an unknown `w`-qubit unitary and `out` output bits
(see the module docstring). -/
structure EvolutionLearner (w out : ℕ) where
  /-- The number of rounds. -/
  R : ℕ
  /-- Ancillas of each round (wires `w, …, w + anc k − 1`). -/
  anc : Fin R → ℕ
  /-- Classical control bits of each round. -/
  cbits : Fin R → ℕ
  /-- The steps of each round, each optionally controlled by a control bit. -/
  template : (k : Fin R) → List (EvolStep w (anc k) × Option (Fin (cbits k)))
  /-- The Boolean circuit computing the control bits of each round from the outcome record. -/
  ctrl : (k : Fin R) → BoolCircuit (∑ j, (w + anc j)) (cbits k)
  /-- The Boolean circuit computing the output bits from the outcome record. -/
  outC : BoolCircuit (∑ j, (w + anc j)) out

namespace EvolutionLearner

variable {w out : ℕ}

/-- The unitary of round `k` for control bits `bits` when the oracle is `U`: the untagged steps
and the steps whose control bit is `1`, in order (the first step is the rightmost factor). -/
def roundUnitary (L : EvolutionLearner w out) (U : Matrix (Qubits w) (Qubits w) ℂ) (k : Fin L.R)
    (bits : Fin (L.cbits k) → Bool) : Matrix (Qubits (w + L.anc k)) (Qubits (w + L.anc k)) ℂ :=
  ((L.template k).filterMap fun s => if s.2.all bits then some (s.1.mat U) else none).reverse.prod

/-- The number of oracle calls: all oracle steps of all round templates. -/
def queriesUsed (L : EvolutionLearner w out) : ℕ :=
  ∑ k, (L.template k).countP fun s => s.1.isOracle

/-- The running time excluding the oracle calls: gate steps, ancilla preparations and classical
Boolean gates. -/
def time (L : EvolutionLearner w out) : ℕ :=
  ∑ k, ((L.template k).countP (fun s => !s.1.isOracle) + L.anc k + (L.ctrl k).size) + L.outC.size

/-- The record of all outcomes of all rounds, concatenated via `finSigmaFinEquiv`. -/
def record (L : EvolutionLearner w out) (z : (k : Fin L.R) → Qubits (w + L.anc k)) :
    Fin (∑ j, (w + L.anc j)) → Bool :=
  fun i => z (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2

/-- The record visible to round `k`: the outcomes of the rounds `< k`, the later bits `0`. -/
def recordBefore (L : EvolutionLearner w out) (z : (k : Fin L.R) → Qubits (w + L.anc k))
    (k : Fin L.R) : Fin (∑ j, (w + L.anc j)) → Bool :=
  fun i => if (finSigmaFinEquiv.symm i).1 < k then z (finSigmaFinEquiv.symm i).1
    (finSigmaFinEquiv.symm i).2 else false

/-- The Born probability `|⟨z_k|V_k|0⋯0⟩|²` of outcome `z k` in round `k`, given the earlier
outcomes, when the oracle is `U`. -/
def roundProb (L : EvolutionLearner w out) (U : Matrix (Qubits w) (Qubits w) ℂ)
    (z : (k : Fin L.R) → Qubits (w + L.anc k)) (k : Fin L.R) : ℝ :=
  Complex.normSq (L.roundUnitary U k ((L.ctrl k).eval (L.recordBefore z k)) (z k) fun _ => false)

/-- The probability that the output bits satisfy `E` when the learner runs with oracle `U`: the sum
over all outcome records of the chain-rule probability of the record times the indicator of `E` at
the output. -/
def successProb (L : EvolutionLearner w out) (U : Matrix (Qubits w) (Qubits w) ℂ)
    (E : (Fin out → Bool) → Prop) : ℝ :=
  ∑ z : (k : Fin L.R) → Qubits (w + L.anc k),
    (∏ k, L.roundProb U z k) * (open Classical in if E (L.outC.eval (L.record z)) then 1 else 0)

end EvolutionLearner

end SYKLearn.Supplement


