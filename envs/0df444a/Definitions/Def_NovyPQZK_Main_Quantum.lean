-- Prove2me | Definitions.Def_NovyPQZK_Main_Quantum
-- name    : NovyPQZK_Main_Quantum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:04.042222+00:00
-- url     : https://prove2.me/theorems/d522a62b-6316-4c04-b2ef-fecb9f4910ef
-- title:
--   Quantum parties with quantum advice, their interaction with classical parties, and QPT
-- statement:
--   **Circuits.** Gates are all unitaries on at most two qubits; a circuit on $N$ wires is a list of gates and $\mathrm{Size}$ counts them (`QAlgorithms_Defs_Circuit`). A classical string $x$ is written into wires $w$ (initially $|0\rangle$) by bit flips; measuring wires in the computational basis gives a string.
--
--   **Quantum parties.** A quantum party $S$ at one security parameter has a register of $\mathrm{inQ}+\mathrm{wkQ}$ qubits: the first $\mathrm{inQ}$ receive an auxiliary input state $\rho$ (register $V$), the others start in a pure **advice** state (the work register $W$, ancillas included). In step $j$ it receives a classical message (written into wires $\mathrm{inW}_j$), applies a circuit, and measures wires $\mathrm{outW}_j$; the outcome is its outgoing message. Its state persists between steps. Step $0$ receives $\mathrm{pack}(\text{input}, \text{first message})$. The run is tracked on subnormalized density matrices: for outcomes $o_0,\dots,o_{K-1}$ the state is $P_{o}U\cdots\rho_{\mathrm{init}}\cdots U^*P_{o}$ and its trace is the probability of the outcomes.
--
--   **Interaction.** Against a classical party $V$ speaking first, $\Pr[V\text{ outputs }1]$ sums over $V$'s coins and the quantum party's outcomes. When the quantum party speaks first against a classical $P$ (the zero-knowledge setting), the induced **channel** maps $\rho$ to the final state of the whole register, averaged over $P$'s coins and all outcomes.
--
--   **QPT** (p. 15, read with p. 7): a family of quantum parties whose size (qubits, steps, wires, gates) is polynomial in $n$ (`IsQPT`) or in $n+|x|$ (`IsQPT₂`), non-uniform, with polynomial-size quantum advice. A **channel algorithm** (simulator) is one unitary circuit with advice, input $\rho$ on its first $\mathrm{inQ}$ qubits, a classical input written into wires, and output the reduced state on its first $\mathrm{outQ}$ qubits (`QChannelAlg`, `IsQPTChan₂`).
--
--   **Formalization Note** Mixed advice and intermediate measurements of a simulator are purified/deferred at polynomial cost. The gate set coincides with the published `TightPQRepetition.Main.smallGates`, which is not imported because its module brings non-uniform classical efficiency notions this mission does not use.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3 pp. 14–15 (quantum procedures, measurement procedures, circuit complexity, QPT), with p. 7 (quantum advice) and pp. 28, 43, 49 (auxiliary inputs)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_NovyPQZK_Main_Classical

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §3,
pp. 14–15 (quantum procedures, computational-basis measurements, circuit complexity, QPT), with the
reading of p. 7 (adversaries hold quantum advice) and of pp. 28, 43, 49 (auxiliary input states).

**Circuits.** Gates are all unitaries on at most two qubits (no finite gate set: exact rewinding and
exact uniform superpositions need exact gates). A computational-basis measurement of some wires and
the loading of a classical string into wires (by bit flips on wires that start in `|0⟩`) are the
only non-unitary steps; ancillas are part of the initial state.

**Quantum parties.** A `QStrategy` is a quantum party at one security parameter: a register of
`inQ + wkQ` qubits whose first `inQ` qubits receive an auxiliary input state (register `V` of
Definition 16) and whose other `wkQ` qubits start in a pure advice state (the work register, with
any ancillas in `|0⟩`). In step `j` it receives a classical message, written into the wires
`inW`, applies a circuit, and measures the wires `outW` in the computational basis; the outcome is
its outgoing message. Its quantum state persists from step to step. Step `0` receives
`pack [input, first message]`.

**QPT** (reading, p. 15 with p. 7): a family of such parties of polynomial size, non-uniform, with
polynomial-size quantum advice; a quantum channel algorithm (`QChannelAlg`, used for simulators)
is a polynomial-size unitary circuit with advice whose output is the reduced state on its first
`outQ` qubits.
-/

open QAlgorithms
open scoped Matrix

/-- The gate set: all unitaries on at most two qubits. -/
def allSmallGates : Set Gate := {g | g.arity ≤ 2 ∧ g.IsUnitary}

/-- Quantum circuits on `N` wires over `allSmallGates`. -/
abbrev QCircuit (N : ℕ) := Circuit allSmallGates N

/-- The wires that `x` flips: wire `w i` is flipped iff bit `i` of `x` is `1`. -/
def flipMask {N : ℕ} (w : List (Fin N)) (x : Bits) : Qubits N :=
  fun a => (w.zip x).any (fun p => decide (p.1 = a) && p.2)

/-- Writing the classical string `x` into the wires `w`: the product of the `X` gates selected by
`x` (a permutation of the computational basis). -/
def loadX {N : ℕ} (w : List (Fin N)) (x : Bits) : Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun y z => if y = (fun a => xor (z a) (flipMask w x a)) then 1 else 0

/-- The classical contents of the wires `w` in the basis state `z`. -/
def readWires {N : ℕ} (w : List (Fin N)) (z : Qubits N) : Bits := w.map z

/-- The diagonal projector onto the basis states whose image under `f` is `v`; `f` reads the
computational basis, so this is one outcome of a computational-basis measurement followed by
classical post-processing. -/
def diagProj {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] (f : ι → α) (v : α) :
    Matrix ι ι ℂ :=
  Matrix.diagonal fun z => if f z = v then 1 else 0

/-- The projector of outcome `c` of the computational-basis measurement of the wires `w`. -/
def outcomeProj {N : ℕ} (w : List (Fin N)) (c : Bits) : Matrix (Qubits N) (Qubits N) ℂ :=
  diagProj (readWires w) c

/-- The pure state `|0…0⟩⟨0…0|` on `m` qubits. -/
def zeroDM (m : ℕ) : Matrix (Qubits m) (Qubits m) ℂ :=
  Matrix.of fun y z => if y = (fun _ => false) ∧ z = (fun _ => false) then 1 else 0

/-- One step of a quantum party. -/
structure RoundStep (N : ℕ) where
  /-- The wires the incoming classical message is written into. -/
  inW : List (Fin N)
  /-- The circuit applied. -/
  circ : QCircuit N
  /-- The wires measured in the computational basis; the outcome is the outgoing message. -/
  outW : List (Fin N)

instance {N : ℕ} : Inhabited (RoundStep N) := ⟨⟨[], [], []⟩⟩

/-- The unitary of a step once the message `x` has been written. -/
noncomputable def RoundStep.op {N : ℕ} (s : RoundStep N) (x : Bits) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  s.circ.unitary * loadX s.inW x

/-- The circuit size of a step: wires loaded, gates, wires measured. -/
def RoundStep.size {N : ℕ} (s : RoundStep N) : ℕ := s.inW.length + s.circ.size + s.outW.length

/-- A quantum party at one security parameter. -/
structure QStrategy where
  /-- Qubits of the auxiliary-input register. -/
  inQ : ℕ
  /-- Qubits of the work register. -/
  wkQ : ℕ
  /-- The initial pure state of the work register: the quantum advice (including ancillas). -/
  advice : Qubits wkQ → ℂ
  /-- The steps; a step beyond this list does nothing and measures nothing. -/
  steps : List (RoundStep (inQ + wkQ))

/-- The number of qubits of a quantum party. -/
abbrev QStrategy.N (S : QStrategy) : ℕ := S.inQ + S.wkQ

/-- Step `j` of a quantum party. -/
def QStrategy.stepAt (S : QStrategy) (j : ℕ) : RoundStep S.N := S.steps.getD j default

/-- Circuit size: qubits, steps, and the sizes of the steps. -/
def QStrategy.size (S : QStrategy) : ℕ :=
  S.inQ + S.wkQ + S.steps.length + (S.steps.map RoundStep.size).sum

/-- A legitimate party: a unit advice vector and repetition-free wire lists. -/
def QStrategy.Valid (S : QStrategy) : Prop :=
  (∑ z, ‖S.advice z‖ ^ 2 = 1) ∧ ∀ s ∈ S.steps, s.inW.Nodup ∧ s.outW.Nodup

/-- QPT, indexed by the security parameter only (the commitment adversaries and the inverters of
Definition 13): polynomial size with quantum advice. -/
def IsQPT (A : ℕ → QStrategy) : Prop :=
  (∀ n, (A n).Valid) ∧ ∃ p : Polynomial ℕ, ∀ n, (A n).size ≤ p.eval n

/-- QPT, indexed by the security parameter `n` and the length `ℓ` of the classical input `x`
(provers of Definition 15, verifiers of Definition 16): polynomial size in `n + ℓ`. -/
def IsQPT₂ (A : ℕ → ℕ → QStrategy) : Prop :=
  (∀ n ℓ, (A n ℓ).Valid) ∧ ∃ p : Polynomial ℕ, ∀ n ℓ, (A n ℓ).size ≤ p.eval (n + ℓ)

/-- The first `a` qubits of a register of `a + b` qubits. -/
def fstPart {a b : ℕ} (z : Qubits (a + b)) : Qubits a := fun i => z (Fin.castAdd b i)

/-- The last `b` qubits of a register of `a + b` qubits. -/
def sndPart {a b : ℕ} (z : Qubits (a + b)) : Qubits b := fun i => z (Fin.natAdd a i)

/-- The initial state `ρ_V ⊗ |advice⟩⟨advice|` of a party given the auxiliary input `ρ`. -/
def QStrategy.initDM (S : QStrategy) (ρ : Matrix (Qubits S.inQ) (Qubits S.inQ) ℂ) :
    Matrix (Qubits S.N) (Qubits S.N) ℂ :=
  Matrix.of fun y z => ρ (fstPart y) (fstPart z) * S.advice (sndPart y) * star (S.advice (sndPart z))

/-- One step on a (subnormalized) density matrix: write `x`, apply the circuit, and keep the branch
of measurement outcome `o`. -/
noncomputable def stepDM {N : ℕ} (s : RoundStep N) (x o : Bits)
    (ρ : Matrix (Qubits N) (Qubits N) ℂ) : Matrix (Qubits N) (Qubits N) ℂ :=
  outcomeProj s.outW o * s.op x * ρ * (s.op x)ᴴ * outcomeProj s.outW o

/-- Running the steps after the outcomes `done`, with the remaining outcomes `rest`; `msg` gives the
message written in at each step from the outcomes so far. -/
noncomputable def QStrategy.runFrom (S : QStrategy) (msg : List Bits → Bits) :
    List Bits → List Bits → Matrix (Qubits S.N) (Qubits S.N) ℂ → Matrix (Qubits S.N) (Qubits S.N) ℂ
  | _, [], ρ => ρ
  | done, o :: rest, ρ =>
      S.runFrom msg (done ++ [o]) rest (stepDM (S.stepAt done.length) (msg done) o ρ)

/-- The subnormalized state after the steps with outcomes `os`, from the auxiliary input `ρ`; its
trace is the probability of these outcomes. -/
noncomputable def QStrategy.run (S : QStrategy) (msg : List Bits → Bits)
    (ρ : Matrix (Qubits S.inQ) (Qubits S.inQ) ℂ) (os : List Bits) :
    Matrix (Qubits S.N) (Qubits S.N) ℂ :=
  S.runFrom msg [] os (S.initDM ρ)

/-- All measurement outcomes of the first `K` steps. -/
abbrev QStrategy.Outs (S : QStrategy) (K : ℕ) := (j : Fin K) → Qubits ((S.stepAt j).outW.length)

/-- The outcomes as a list of strings. -/
def QStrategy.outList {S : QStrategy} {K : ℕ} (o : S.Outs K) : List Bits :=
  List.ofFn fun j => List.ofFn (o j)

/-- The messages written into a quantum party talking to a classical party with message function
`cmsg` (from the quantum party's messages so far): step `0` receives `pack [input, cmsg []]`. -/
def msgFor (input : Bits) (cmsg : List Bits → Bits) (done : List Bits) : Bits :=
  if done = [] then pack [input, cmsg []] else cmsg done

/-- A classical party `P` that speaks second in every round: its message after the quantum party's
messages `done` (nothing before the first one). -/
def responderMsg (P : Party) (inP : Bits) (c : CoinSpace (P.coins inP)) (done : List Bits) : Bits :=
  if done = [] then [] else P.msg inP c done

/-- The probability that the classical party `V` (speaking first in each round, input `inV`)
outputs `1` after `r` rounds with the quantum party `Q` (classical input `inQ`, auxiliary input
register in `|0⟩`), over `V`'s coins and `Q`'s measurements. -/
noncomputable def acceptProbQ (V : Party) (inV : Bits) (Q : QStrategy) (inQ : Bits) (r : ℕ) : ℝ :=
  avgOver (CoinSpace (V.coins inV)) fun c =>
    ∑ o : Q.Outs r,
      if V.msg inV c (QStrategy.outList o) = [true] then
        (Q.run (msgFor inQ (V.msg inV c)) (zeroDM Q.inQ) (QStrategy.outList o)).trace.re
      else 0

/-- The channel induced on the quantum party `Q` (speaking first in each round, classical input
`inQ`) by `r` rounds with the classical party `P` (input `inP`): on auxiliary input `ρ`, the final
state of the whole register of `Q`, averaged over `P`'s coins and `Q`'s measurement outcomes.
`Q` takes `r + 1` steps: the last one receives `P`'s last message. -/
noncomputable def interactionChannel (P : Party) (inP : Bits) (Q : QStrategy) (inQ : Bits) (r : ℕ)
    (ρ : Matrix (Qubits Q.inQ) (Qubits Q.inQ) ℂ) : Matrix (Qubits Q.N) (Qubits Q.N) ℂ :=
  avgOver (CoinSpace (P.coins inP)) fun c =>
    ∑ o : Q.Outs (r + 1), Q.run (msgFor inQ (responderMsg P inP c)) ρ (QStrategy.outList o)

/-- The reduced state on the first `m` qubits of a state on `N ≥ m` qubits (partial trace over the
others). -/
def keepFirst {N m : ℕ} (h : m ≤ N) (ρ : Matrix (Qubits N) (Qubits N) ℂ) :
    Matrix (Qubits m) (Qubits m) ℂ :=
  Matrix.of fun y z =>
    ∑ e : Qubits N, if (∀ i : Fin m, e (Fin.castLE h i) = y i) then
      ρ e (fun i => if hi : i.val < m then z ⟨i.val, hi⟩ else e i) else 0

/-- A quantum algorithm computing a channel: the auxiliary input on the first `inQ` qubits, the
advice on the other `wkQ`, the classical input written into `inW`, one unitary circuit, and the
output on the first `outQ` qubits (intermediate measurements are deferred). -/
structure QChannelAlg where
  /-- Qubits of the auxiliary input. -/
  inQ : ℕ
  /-- Work qubits. -/
  wkQ : ℕ
  /-- Output qubits. -/
  outQ : ℕ
  /-- The output is part of the register. -/
  hout : outQ ≤ inQ + wkQ
  /-- The advice state of the work qubits. -/
  advice : Qubits wkQ → ℂ
  /-- The wires the classical input is written into. -/
  inW : List (Fin (inQ + wkQ))
  /-- The circuit. -/
  circ : QCircuit (inQ + wkQ)

/-- The channel computed on classical input `x`. -/
noncomputable def QChannelAlg.channel (S : QChannelAlg) (x : Bits)
    (ρ : Matrix (Qubits S.inQ) (Qubits S.inQ) ℂ) : Matrix (Qubits S.outQ) (Qubits S.outQ) ℂ :=
  let U := S.circ.unitary * loadX S.inW x
  let init : Matrix (Qubits (S.inQ + S.wkQ)) (Qubits (S.inQ + S.wkQ)) ℂ :=
    Matrix.of fun y z => ρ (fstPart y) (fstPart z) * S.advice (sndPart y) * star (S.advice (sndPart z))
  keepFirst S.hout (U * init * Uᴴ)

/-- Size of a channel algorithm. -/
def QChannelAlg.size (S : QChannelAlg) : ℕ := S.inQ + S.wkQ + S.inW.length + S.circ.size

/-- A legitimate channel algorithm: unit advice, repetition-free input wires. -/
def QChannelAlg.Valid (S : QChannelAlg) : Prop :=
  (∑ z, ‖S.advice z‖ ^ 2 = 1) ∧ S.inW.Nodup

/-- QPT channel algorithms indexed by the security parameter and the classical input length. -/
def IsQPTChan₂ (A : ℕ → ℕ → QChannelAlg) : Prop :=
  (∀ n ℓ, (A n ℓ).Valid) ∧ ∃ p : Polynomial ℕ, ∀ n ℓ, (A n ℓ).size ≤ p.eval (n + ℓ)

/-- Transport of a matrix on `m` qubits to `m'` qubits along `m = m'`. -/
def qcast {m m' : ℕ} (h : m = m') (ρ : Matrix (Qubits m) (Qubits m) ℂ) :
    Matrix (Qubits m') (Qubits m') ℂ :=
  Matrix.reindex (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))
    (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) ρ

end NovyPQZK.Main


