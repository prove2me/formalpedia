-- Prove2me | Definitions.Def_FourMsgQMA_Core
-- name    : FourMsgQMA_Core
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:06.22128+00:00
-- url     : https://prove2.me/theorems/a0f81b7e-265b-4c4d-9373-986d9b79073a
-- title:
--   Honest quantum cores over $\{H,S,T,X,\mathrm{CNOT}\}$ and their acceptance on mixed states
-- statement:
--   The honest QPT prover of §3.3 is modelled as a **quantum core** with a classical controller. A core has $n$ qubits, a list of rounds and a random tape. Round $j$ writes a classical string, computed by the controller from what it has seen, into designated wires by $X$ gates, applies a layered circuit over $\{H,S,T,X,\mathrm{CNOT}\}$, and measures designated wires in the computational basis. The controller then computes the answer of round $j$. This is the published adversary model `TightPQRepetition.Main.Strategy` with a finite gate set.
--
--   For a verifier $V$, an outcome sequence $f$ determines the classical transcript and a Kraus operator $K_f$, the product of the round operators. The acceptance probability from an initial density operator $\rho$ is
--   $$
--   \Pr[\text{accept}]=\mathbb E_{r,\,u}\sum_{f:\,V\text{ accepts}}\operatorname{Re}\operatorname{tr}\big(K_f\,\rho\,K_f^{\dagger}\big),
--   $$
--   averaged over the verifier's coins $r$ and the prover's tape $u$. For $\rho=|\psi\rangle\langle\psi|$ the weight is $\|K_f\psi\|^2$, the one used by the published `Strategy.eventProb`.
--
--   The module also fixes the state $\rho_{i_1}\otimes\rho_{i_2}\otimes\cdots\otimes|0\cdots0\rangle\langle0\cdots0|$ that places given registers on the first wires of a core, in order. It is the zero matrix when the core is too small.
--
--   **Formalization Note** Pinned-down version (operator request): the honest prover's initial state is the honest resource $\omega$ ("Initially $\rho_0=\omega\in W_\Pi(u)$", p.11), a density operator, so acceptance is computed from Kraus operators.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, p.11 (PDF 13)

import Mathlib
import Definitions.Def_FourMsgQMA_ComputedOn

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), §3.3 (p.11, PDF 13): the honest QPT
prover `(a_j, ρ_j) ← P_j(u, ρ_{j-1}, q_j)`, started from `ρ_0 = ω`.

Pinned-down version (operator request). The honest prover is a quantum **core** over the finite
gate set `H, S, T, X, CNOT` (the published `QAlgorithms.Complexity.Instr`), run exactly like the
published adversary model `TightPQRepetition.Main.Strategy` (round `j`: write a classical string
into the wires `inW`, apply a layered circuit, measure the wires `outW`; a classical controller
turns what it has seen into the next core input and the next answer). Unlike an adversary, it
starts from a density operator, the honest resource. Its acceptance probability is computed from
the Kraus operators of the run, so it is linear in the initial state.
-/

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main
open scoped Matrix

/-- The matrix of a layered circuit over `H, S, T, X, CNOT`: column `z` is the output of the
circuit on the basis state `|z⟩`. -/
noncomputable def layeredMatrix {n : ℕ} (c : Layered n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => runLayered c (fun w => if w = z then 1 else 0) y

/-- One round of an honest core. -/
structure CoreStep (n : ℕ) where
  /-- The wires the incoming classical string is written into. -/
  inW : List (Fin n)
  /-- The layered circuit applied in this round. -/
  circ : Layered n
  /-- The wires measured to produce the core's classical output. -/
  outW : List (Fin n)

/-- An honest quantum core: `n` qubits, its rounds, and the length of its classical random tape. -/
structure Core where
  /-- Number of qubits. -/
  n : ℕ
  /-- The rounds. A round beyond this list does nothing and measures nothing. -/
  steps : List (CoreStep n)
  /-- Length of the classical random tape. -/
  tape : ℕ

/-- Round `j` of a core. -/
def Core.stepAt (S : Core) (j : ℕ) : CoreStep S.n := S.steps.getD j ⟨[], [], []⟩

/-- The number of wires measured in round `j`. -/
def Core.outLen (S : Core) (j : ℕ) : ℕ := (S.stepAt j).outW.length

/-- Size of a core: qubits, tape, rounds, wires and gates. -/
def Core.size (S : Core) : ℕ :=
  S.n + S.tape + S.steps.length +
    (S.steps.map fun s => s.inW.length + (s.circ.map List.length).sum + s.outW.length).sum

/-- The encoding of a core as a bit string (qubit count, tape length, and every round's input
wires, layered circuit in the published encoding `encCirc`, and output wires). -/
def Core.encode (S : Core) : Str :=
  encNat S.n ++ encNat S.tape ++
    encStr (S.steps.map fun s =>
      encStr [encStr (s.inW.map fun w => encNat w.val), encCirc s.circ,
        encStr (s.outW.map fun w => encNat w.val)])

/-- The classical record and the accumulated Kraus operator of a run. -/
structure CoreRun (n : ℕ) where
  /-- The product of the round operators so far (the Kraus operator of the outcomes so far). -/
  op : Matrix (Qubits n) (Qubits n) ℂ
  /-- The `(message, core answer)` pairs so far. -/
  hist : List (Bits × Bits)
  /-- The answers sent so far. -/
  answers : List Bits

/-- One round of an honest run, mirroring `TightPQRepetition.Main.Strategy.runStep`: the verifier's
message is `query j answers`; the controller `toCore` computes the string written into the core;
the core applies its circuit; the measurement of `outW` has outcome `c`; the controller
`toVerifier` computes the answer. -/
noncomputable def Core.runStep (S : Core) (toCore toVerifier : ℕ → Bits → Bits)
    (query : ℕ → List Bits → Bits) (u : Bits) (st : CoreRun S.n) (c : Bits) : CoreRun S.n :=
  let j := st.hist.length
  let q := query j st.answers
  let x := toCore j (pack (controllerView u st.hist ++ [q]))
  let s := S.stepAt j
  let hist' := st.hist ++ [(q, c)]
  { op := outcomeProj s.outW c * (layeredMatrix s.circ * loadX s.inW x) * st.op
    hist := hist'
    answers := st.answers ++ [toVerifier j (pack (controllerView u hist'))] }

/-- The run with core outcomes `cs` and tape `u`. -/
noncomputable def Core.run (S : Core) (toCore toVerifier : ℕ → Bits → Bits)
    (query : ℕ → List Bits → Bits) (u : Bits) (cs : List Bits) : CoreRun S.n :=
  cs.foldl (S.runStep toCore toVerifier query u) ⟨1, [], []⟩

/-- The transcript `(q_1, a_1, …)` of a run. -/
def CoreRun.transcript {n : ℕ} (st : CoreRun n) : List (Bits × Bits) :=
  (st.hist.map Prod.fst).zip st.answers

open Classical in
/-- The probability that the verifier `V` accepts its interaction with the honest core `S` and the
controllers `toCore`, `toVerifier`, when the core starts in the density operator `ρ`: an average
over the verifier's coins and the prover's tape, and over all measurement outcomes `f` of the
weight `Re tr(K_f ρ K_fᴴ)`. For a pure `ρ = |ψ⟩⟨ψ|` this is the weight `‖K_f ψ‖²` used by the
published `Strategy.eventProb`. -/
noncomputable def Core.acceptMixed (S : Core) (toCore toVerifier : ℕ → Bits → Bits)
    (V : Verifier) (lam : ℕ) (ρ : Matrix (Qubits S.n) (Qubits S.n) ℂ) : ℝ :=
  avgCoins (V.coins lam) fun r => avgCoins S.tape fun u =>
    ∑ f : (j : Fin (V.rounds lam)) → Qubits (S.outLen j),
      let st := S.run toCore toVerifier (V.query lam r) u (List.ofFn fun j => toBits (f j))
      if V.verdict lam r st.transcript = true then
        (Matrix.trace (st.op * ρ * st.opᴴ)).re else 0

/-- The value of wire `m` of a basis state, `false` beyond the register. -/
def wireAt {n : ℕ} (y : Qubits n) (m : ℕ) : Bool := if h : m < n then y ⟨m, h⟩ else false

/-- The matrix entry `⟨y| ρ_{i₁} ⊗ ρ_{i₂} ⊗ ⋯ |z⟩` of the tensor product of the registers listed in
`blocks`, laid out consecutively from wire `o` on (block `i` occupies `w i` wires). -/
noncomputable def tensorEntry {ι : Type} (w : ι → ℕ)
    (ρ : (i : ι) → Matrix (Qubits (w i)) (Qubits (w i)) ℂ) :
    List ι → ℕ → (ℕ → Bool) → (ℕ → Bool) → ℂ
  | [], _, _, _ => 1
  | i :: rest, o, y, z =>
      ρ i (fun j => y (o + j)) (fun j => z (o + j)) * tensorEntry w ρ rest (o + w i) y z

/-- The initial state of an `n`-qubit core holding the registers of `blocks` in its first wires,
in order, and `|0⟩` on every other wire: `ρ_{i₁} ⊗ ρ_{i₂} ⊗ ⋯ ⊗ |0…0⟩⟨0…0|`. If the core is too
small to hold the registers, the state is the zero matrix (the run then never accepts). -/
noncomputable def loadedState {ι : Type} (w : ι → ℕ)
    (ρ : (i : ι) → Matrix (Qubits (w i)) (Qubits (w i)) ℂ) (blocks : List ι) (n : ℕ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z =>
    if (blocks.map w).sum ≤ n ∧
        (∀ m : Fin n, (blocks.map w).sum ≤ m.val → y m = false ∧ z m = false) then
      tensorEntry w ρ blocks 0 (wireAt y) (wireAt z) else 0

end FourMsgQMA


