-- Prove2me | Definitions.Def_ContractionLemma_Supplement_Quantum
-- name    : ContractionLemma_Supplement_Quantum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:19:03.383336+00:00
-- url     : https://prove2.me/theorems/cd71e4b6-9b12-495f-8609-a26cab898645
-- title:
--   Gate sets, quantum circuits and the quantum time classes (§2.5, Definition 2.9)
-- statement:
--   A **gate set** $\mathcal G$ is a fixed finite set of unitary gates, each acting on a constant number of qubits, whose matrix entries are algebraic numbers. A **$\mathcal G$-circuit** acts on $q$ qubits initialized to a computational-basis state by a sequence of $s$ gates from $\mathcal G$, each applied to distinct qubits; it accepts when designated output qubits, measured in the computational basis, show a designated pattern. Its final state is $|\psi\rangle=g_s\cdots g_1|x\rangle$ and its acceptance probability is $\langle\psi|\Pi|\psi\rangle$.
--
--   A family $(Q_n)$ is **uniform with $O(t)$ gates and ancillas** if a deterministic algorithm outputs $Q_n$ on input $1^n$ in time $\mathrm{poly}(n+t(n))$, and $Q_n$ has at most $c\,(t(n)+1)$ gates and $c\,(t(n)+1)$ ancillas. With $p_Q(x)$ the acceptance probability of $Q_{|x|}$ on input $x$ (Definition 2.9):
--
--   1. $L\in\mathsf{BQTIME}[t]$ if $p_Q(x)\ge2/3$ for $x\in L$ and $p_Q(x)\le1/3$ for $x\notin L$;
--   2. $L\in\mathsf{PostBQTIME}[t]$ if a designated postselection qubit is measured as $1$ with positive probability on every input, and the conditional acceptance probability is at least $2/3$ on $L$ and at most $1/3$ off $L$;
--   3. $L\in\mathsf{QCMATIME}[t]$ if $Q_n$ also reads a classical witness on at most $c\,(t(n)+1)$ qubits, some witness giving at least $2/3$ on $L$ and every witness at most $1/3$ off $L$;
--   4. $L\in\mathsf{QMATIME}[t,w]$ if $Q_n$ also reads a quantum witness, a unit vector on $w(n)$ qubits, with the same thresholds.
--
--   These are the quantum classes of $\mathcal C_t$ and of Theorems 11–13; all statements hold for every fixed gate set.
--
--   **Formalization Note** States are amplitude functions on $\{0,1\}^q$. The register of $Q_n$ is the input, then the witness, then the ancillas, which start in a basis state chosen by the family.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), §2.5, p.20 ("Quantum circuits"); Definition 2.9, p.21

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Supplement_Common

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **A gate set** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256 049caea1…),
§2.5, p.20: "a fixed finite set of unitary gates, each acting on a constant number of qubits, whose
matrix entries are algebraic numbers."

Gate `g` acts on `arity g` qubits; its matrix is indexed by the basis states `Fin (arity g) → Bool`
of those qubits, is unitary, and has algebraic entries. -/
structure GateSet where
  /-- the number of gates -/
  size : ℕ
  /-- the number of qubits of each gate -/
  arity : Fin size → ℕ
  /-- the matrix of each gate -/
  mat : (g : Fin size) → Matrix (Fin (arity g) → Bool) (Fin (arity g) → Bool) ℂ
  /-- every gate is unitary -/
  unitary : ∀ g, mat g ∈ Matrix.unitaryGroup (Fin (arity g) → Bool) ℂ
  /-- every entry is algebraic -/
  algebraic : ∀ g a b, IsAlgebraic ℚ (mat g a b)

namespace GateSet

/-- An application of a gate of `G` to distinct qubits of a `q`-qubit register. -/
structure App (G : GateSet) (q : ℕ) where
  /-- the gate -/
  gate : Fin G.size
  /-- the qubits it acts on, in order -/
  targets : Fin (G.arity gate) → Fin q
  /-- the qubits are distinct -/
  inj : Function.Injective targets

variable (G : GateSet)

/-- A state of `q` qubits, as amplitudes on the computational basis `Fin q → Bool`. -/
abbrev QState (q : ℕ) := (Fin q → Bool) → ℂ

/-- Apply one gate application to a state: on basis state `y`, the new amplitude sums the gate
matrix entry `U[y|targets, b]` times the amplitude of `y` with its target qubits replaced by `b`. -/
noncomputable def applyApp {q : ℕ} (a : G.App q) (ψ : QState q) : QState q :=
  fun y => ∑ b : Fin (G.arity a.gate) → Bool,
    G.mat a.gate (fun i => y (a.targets i)) b *
      ψ (fun j => if h : ∃ i, a.targets i = j then b h.choose else y j)

/-- Apply a sequence of gates, first to last. -/
noncomputable def applyAll {q : ℕ} (gates : List (G.App q)) (ψ : QState q) : QState q :=
  gates.foldl (fun φ a => G.applyApp a φ) ψ

/-- The computational-basis state `|x⟩`. -/
def basis {q : ℕ} (x : Fin q → Bool) : QState q := fun y => if y = x then 1 else 0

open scoped Classical in
/-- The probability that measuring `ψ` in the computational basis shows the pattern `pat` (each pair
`(j, b)` requires qubit `j` to show `b`). -/
noncomputable def patProb {q : ℕ} (ψ : QState q) (pat : List (Fin q × Bool)) : ℝ :=
  ∑ y : Fin q → Bool, if ∀ pr ∈ pat, y pr.1 = pr.2 then ‖ψ y‖ ^ 2 else 0

end GateSet

/-- **A `G`-circuit with its input** (§2.5, p.20): `q` qubits initialized to the computational-basis
state `input`, a sequence of gates, the accepting pattern `acc` on designated output qubits, and a
postselection pattern `post` (Theorem 11). -/
structure QCircuit (G : GateSet) where
  /-- number of qubits -/
  q : ℕ
  /-- the gates in order -/
  gates : List (G.App q)
  /-- the computational-basis input -/
  input : Fin q → Bool
  /-- the accepting pattern -/
  acc : List (Fin q × Bool)
  /-- the postselection pattern -/
  post : List (Fin q × Bool)

namespace QCircuit

variable {G : GateSet}

/-- The number of gates `s`. -/
def size (Q : QCircuit G) : ℕ := Q.gates.length

/-- The final state `g_s ⋯ g_1 |x⟩`. -/
noncomputable def final (Q : QCircuit G) : GateSet.QState Q.q := G.applyAll Q.gates (GateSet.basis Q.input)

/-- The acceptance probability `⟨ψ|Π|ψ⟩`. -/
noncomputable def accProb (Q : QCircuit G) : ℝ := GateSet.patProb Q.final Q.acc

/-- The probability of the postselection event. -/
noncomputable def postProb (Q : QCircuit G) : ℝ := GateSet.patProb Q.final Q.post

/-- The probability of acceptance together with the postselection event. -/
noncomputable def accPostProb (Q : QCircuit G) : ℝ := GateSet.patProb Q.final (Q.acc ++ Q.post)

/-- The encoding of a pattern. -/
def encodePat {q : ℕ} (pat : List (Fin q × Bool)) : List Bool :=
  Encoding.encodeList (fun pr : Fin q × Bool => Encoding.encodeList id [countWord pr.1, [pr.2]]) pat

/-- The encoding of a circuit: the number of qubits, each gate as its index and its target qubits
(binary), the input bits, and the two patterns. Its length is the `L` of Theorem 11. -/
def encode (Q : QCircuit G) : List Bool :=
  Encoding.encodeList id
    [countWord Q.q,
      Encoding.encodeList (fun a : G.App Q.q => Encoding.encodeList id
        [countWord a.gate, Encoding.encodeList (fun i => countWord (a.targets i))
          (List.finRange (G.arity a.gate))]) Q.gates,
      List.ofFn Q.input, encodePat Q.acc, encodePat Q.post]

end QCircuit

/-- **The circuit `Q_n` of a uniform family on inputs of length `n`** (§2.5–2.6, Definition 2.9,
pp.20–21): `n` input qubits, `wq` witness qubits, `anc` ancillas initialized to `ancInit`, the gates,
the accepting pattern and a postselection pattern.

**Formalization Note.** The register is `Fin (n + wq + anc)`: inputs first, then the witness, then the
ancillas. Ancillas start in a computational-basis state chosen by the family. A classical witness is a
basis state of the witness register (Definition 2.9 QCMATIME), a quantum witness an arbitrary unit
vector (QMATIME). -/
structure QFam (G : GateSet) (n : ℕ) where
  /-- number of witness qubits -/
  wq : ℕ
  /-- number of ancillas -/
  anc : ℕ
  /-- the gates -/
  gates : List (G.App (n + wq + anc))
  /-- the initial values of the ancillas -/
  ancInit : Fin anc → Bool
  /-- the accepting pattern -/
  acc : List (Fin (n + wq + anc) × Bool)
  /-- the postselection pattern -/
  post : List (Fin (n + wq + anc) × Bool)

namespace QFam

variable {G : GateSet} {n : ℕ}

/-- The initial state on input `x` with witness state `φ`: `|x⟩ ⊗ φ ⊗ |ancInit⟩`. -/
noncomputable def initState (F : QFam G n) (x : List Bool) (φ : GateSet.QState F.wq) :
    GateSet.QState (n + F.wq + F.anc) := fun y =>
  if (∀ i : Fin n, y (Fin.castAdd F.anc (Fin.castAdd F.wq i)) = x.getD i false) ∧
      (∀ i : Fin F.anc, y (Fin.natAdd (n + F.wq) i) = F.ancInit i) then
    φ (fun i => y (Fin.castAdd F.anc (Fin.natAdd n i)))
  else 0

/-- The acceptance probability on input `x` with witness state `φ`. -/
noncomputable def accProb (F : QFam G n) (x : List Bool) (φ : GateSet.QState F.wq) : ℝ :=
  GateSet.patProb (G.applyAll F.gates (F.initState x φ)) F.acc

/-- The probability of the postselection event on input `x` with witness state `φ`. -/
noncomputable def postProb (F : QFam G n) (x : List Bool) (φ : GateSet.QState F.wq) : ℝ :=
  GateSet.patProb (G.applyAll F.gates (F.initState x φ)) F.post

/-- The probability of acceptance and postselection on input `x` with witness state `φ`. -/
noncomputable def accPostProb (F : QFam G n) (x : List Bool) (φ : GateSet.QState F.wq) : ℝ :=
  GateSet.patProb (G.applyAll F.gates (F.initState x φ)) (F.acc ++ F.post)

/-- The encoding of `Q_n`, output by the uniformity algorithm. -/
def encode (F : QFam G n) : List Bool :=
  Encoding.encodeList id
    [countWord n, countWord F.wq, countWord F.anc,
      Encoding.encodeList (fun a : G.App (n + F.wq + F.anc) => Encoding.encodeList id
        [countWord a.gate, Encoding.encodeList (fun i => countWord (a.targets i))
          (List.finRange (G.arity a.gate))]) F.gates,
      List.ofFn F.ancInit, QCircuit.encodePat F.acc, QCircuit.encodePat F.post]

end QFam

/-- **A uniform family with `O(t)` gates and ancillas** (§2.5–2.6, pp.20–21): a deterministic
algorithm outputs `Q_n` on input `1^n` in time `poly(n + t(n))` ("uniformity allows time
`poly(n + t(n))`", p.21), and `Q_n` has at most `c·(t(n)+1)` gates and at most `c·(t(n)+1)`
ancillas (`O(t)` as `c·(t(n)+1)`, as for the clocks of the classical classes; at `n = 0` a bound
`c·t(0) = 0` would force `[] ∈ L` in BQTIME). -/
def UniformFam (G : GateSet) (t : ℕ → ℕ) (Qf : (n : ℕ) → QFam G n) (c : ℕ) : Prop :=
  (∃ (U : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (out : Fin U.tapeCount) (C : ℕ), ∀ n,
      RunsInTime U out (List.replicate n true) (Qf n).encode (C * ((n : ℝ) + t n + 1) ^ C)) ∧
  ∀ n, (Qf n).gates.length ≤ c * (t n + 1) ∧ (Qf n).anc ≤ c * (t n + 1)

/-- The witness state of the empty witness register. -/
def noWitness : GateSet.QState 0 := fun _ => 1

/-- **BQTIME[t]** for the gate set `G` (Definition 2.9). -/
def BQTIME (G : GateSet) (t : ℕ → ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (Qf : (n : ℕ) → QFam G n) (c : ℕ) (hw : ∀ n, (Qf n).wq = 0), UniformFam G t Qf c ∧
    ∀ x : List Bool,
      (L x → (2 : ℝ) / 3 ≤ (Qf x.length).accProb x (hw x.length ▸ noWitness)) ∧
      (¬ L x → (Qf x.length).accProb x (hw x.length ▸ noWitness) ≤ 1 / 3)

/-- **PostBQTIME[t]** for `G` (Definition 2.9): a designated postselection qubit, measured as `1`
with positive probability on every input; conditioned on it, acceptance is at least `2/3` on `L` and
at most `1/3` off `L`. -/
def PostBQTIME (G : GateSet) (t : ℕ → ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (Qf : (n : ℕ) → QFam G n) (c : ℕ) (hw : ∀ n, (Qf n).wq = 0), UniformFam G t Qf c ∧
    (∀ n, ∃ j, (Qf n).post = [(j, true)]) ∧
    ∀ x : List Bool,
      0 < (Qf x.length).postProb x (hw x.length ▸ noWitness) ∧
      (L x → (2 : ℝ) / 3 * (Qf x.length).postProb x (hw x.length ▸ noWitness) ≤
        (Qf x.length).accPostProb x (hw x.length ▸ noWitness)) ∧
      (¬ L x → (Qf x.length).accPostProb x (hw x.length ▸ noWitness) ≤
        1 / 3 * (Qf x.length).postProb x (hw x.length ▸ noWitness))

/-- **QCMATIME[t]** for `G` (Definition 2.9): `Q_n` also reads a classical witness on at most
`c·t(n)` witness qubits; on `L` some witness gives acceptance at least `2/3`, off `L` every witness
gives at most `1/3`. -/
def QCMATIME (G : GateSet) (t : ℕ → ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (Qf : (n : ℕ) → QFam G n) (c : ℕ), UniformFam G t Qf c ∧
    (∀ n, (Qf n).wq ≤ c * (t n + 1)) ∧
    ∀ x : List Bool,
      (L x → ∃ w : Fin (Qf x.length).wq → Bool,
        (2 : ℝ) / 3 ≤ (Qf x.length).accProb x (GateSet.basis w)) ∧
      (¬ L x → ∀ w : Fin (Qf x.length).wq → Bool,
        (Qf x.length).accProb x (GateSet.basis w) ≤ 1 / 3)

/-- **QMATIME[t, w]** for `G` (Definition 2.9): `Q_n` also reads a quantum witness, a unit vector
on `w(n)` qubits; on `L` some state gives acceptance at least `2/3`, off `L` every state gives at most
`1/3`. -/
def QMATIME (G : GateSet) (t w : ℕ → ℕ) (L : List Bool → Prop) : Prop :=
  ∃ (Qf : (n : ℕ) → QFam G n) (c : ℕ), UniformFam G t Qf c ∧
    (∀ n, (Qf n).wq = w n) ∧
    ∀ x : List Bool,
      (L x → ∃ φ : GateSet.QState (Qf x.length).wq, ∑ y, ‖φ y‖ ^ 2 = 1 ∧
        (2 : ℝ) / 3 ≤ (Qf x.length).accProb x φ) ∧
      (¬ L x → ∀ φ : GateSet.QState (Qf x.length).wq, ∑ y, ‖φ y‖ ^ 2 = 1 →
        (Qf x.length).accProb x φ ≤ 1 / 3)

end ContractionLemma.Supplement


