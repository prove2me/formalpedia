-- Prove2me | Definitions.Def_LIPAlgorithm_Supplement_qProb
-- name    : LIPAlgorithm_Supplement_qProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:53:52.476477+00:00
-- url     : https://prove2.me/theorems/fe78be05-93c5-455c-a318-1b2f69608194
-- title:
--   The QRAM model: a TM2 controller with quantum calls over $\{H,T,\mathrm{CNOT}\}$ and QRAM gates, its cost, QRAM size and Born-rule success probability
-- statement:
--   This definition fixes the **QRAM model** of §8.1–8.2 in which the quantum results of the paper are stated: a classical controller that writes a quantum random-access memory and calls quantum circuits that read it in superposition.
--
--   1. **Controller.** A Turing machine with several stacks over the alphabet $\{0,1\}$ (Mathlib's TM2, the model of the published `RunsWithin`), fixed before the input. It issues a request by halting with an encoded request on its output stack. It is then resumed at its start label with its stacks and internal state kept; the request is removed and the answer is pushed on its input stack.
--   2. **Requests.** *halt with output* $y$; *write* a bit string $x$ into cell $j$ of the QRAM table (overwrite if $j$ is in the table, append if $j$ equals its length); *query* a circuit $C$ on $q$ wires.
--   3. **Quantum calls.** The circuit is a list of gates from the fixed set $\{H, T, \mathrm{CNOT}\}$ together with QRAM gates. A QRAM gate on an address register $j$ and a data register $b$ acts as
--   $$|j\rangle|b\rangle\mapsto|j\rangle|b\oplus x_j\rangle,$$
--   where $x_j$ is cell $j$ of the current table ($x_j=0$ outside the table). The circuit is applied to $|0^q\rangle$ and all wires are measured in the computational basis: outcome $z$ has probability $|\langle z|C|0^q\rangle|^2$, and the bits of $z$ are the answer.
--   4. **Cost and memory.** The cost of a run is the number of controller steps plus, for every query, the number of gates of its circuit (each QRAM call costs one unit). The QRAM size of a run is the number of cells of its table.
--   5. **Probability.** $\mathrm{qProb}(M, \mathit{inp}, B, S, E)$ is the probability, over the Born-rule outcomes of all quantum calls, that the run of $M$ on input $\mathit{inp}$, started with an empty table, halts with cost at most $B$, never holds more than $S$ cells, and outputs a string satisfying $E$. A malformed request ends its branch unsuccessfully.
--
--   The statement $\mathrm{qProb}(M,\mathit{inp},B,S,\mathrm{True})=1$ says that every branch of positive probability halts within cost $B$ and QRAM size $S$. Theorems 8.7 and 8.15 are stated in this model.
--
--   **Formalization Note** The gate set is finite with exact entries, so an arbitrary unitary is not a unit-cost gate. The controller writes every circuit and every cell explicitly, so their description length is charged too. Classical coins are obtained by measuring Hadamard states. The Hadamard and $T$ matrices, the embedding of a one-qubit gate, $|0^q\rangle$, the action of a matrix and the Born probability come from the published `QAlgorithms_Defs_Basic`, `QAlgorithms_Defs_Gates` and `QAlgorithms_Defs_Circuit`; the self-delimiting number encoding from `ExponomialAssortment_FPTAS_Machine`. Every round costs at least one controller step, so the round limit $B+1$ in the recursion cuts no run of cost at most $B$.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), §8.1, p.42 (PDF p.45); Definition 8.3, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_LIPAlgorithm_encInst

open ExponomialAssortment.FPTAS
open QAlgorithms
open scoped Classical

namespace LIPAlgorithm

namespace Supplement

/-- A gate of a submitted circuit, on numbered wires: Hadamard on wire `i`, `T` on wire `i`, CNOT with
control `c` and target `t`, and a QRAM call with address register `addr` and data register `dat`
(wire lists, least significant bit first).
Aggarwal, Jiang, Li, Liu, *An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem*, STOC 2027
submission (manuscript sha256 61ee52aa…), §8.1, p.42 (PDF p.45) ("the standard quantum circuit model")
and Definition 8.3, p.43 (PDF p.46) (QRAM).

**Formalization Note.** The gate set `{H, T, CNOT}` is a fixed finite universal set with exact
entries; arbitrary unitaries are not unit-cost gates. -/
inductive QGate where
  | H (i : ℕ)
  | T (i : ℕ)
  | CNOT (c t : ℕ)
  | QRAM (addr dat : List ℕ)

/-- A gate is well formed on `q` wires: its wires are below `q`, CNOT's two wires differ, and the
address and data registers of a QRAM call are disjoint lists of distinct wires (this makes every gate
a permutation or a unitary). -/
def QGate.Valid (q : ℕ) : QGate → Prop
  | .H i => i < q
  | .T i => i < q
  | .CNOT c t => c < q ∧ t < q ∧ c ≠ t
  | .QRAM a d => (∀ i ∈ a ++ d, i < q) ∧ (a ++ d).Nodup

/-- Bit `i` of the basis string `z` (`false` beyond the register). -/
def getb {q : ℕ} (z : Qubits q) (i : ℕ) : Bool :=
  if h : i < q then z ⟨i, h⟩ else false

/-- The number written by the wires `a` of `z`, least significant wire first. -/
def bval {q : ℕ} (z : Qubits q) : List ℕ → ℕ
  | [] => 0
  | i :: r => (if getb z i then 1 else 0) + 2 * bval z r

/-- XOR the bit string `v` into the wires `d` of `z`: wire `d[k]` is flipped by `v[k]` (bits of `v`
beyond its length are `0`, bits beyond `d`'s length are ignored). -/
def xorReg {q : ℕ} (z : Qubits q) (d : List ℕ) (v : List Bool) : Qubits q :=
  fun w => if w.val ∈ d then xor (z w) (v.getD (d.idxOf w.val) false) else z w

/-- Definition 8.3 on basis strings: `|j⟩|b⟩ ↦ |j⟩|b ⊕ x_j⟩`, with `j` the number in the address
wires and `x_j` cell `j` of the current table (`x_j = 0` for `j` outside the table). -/
def qramMap {q : ℕ} (tab : List (List Bool)) (a d : List ℕ) (z : Qubits q) : Qubits q :=
  xorReg z d (tab.getD (bval z a) [])

/-- The permutation matrix of a map of basis strings: `|x⟩ ↦ |f x⟩`. -/
noncomputable def permMat {q : ℕ} (f : Qubits q → Qubits q) : Matrix (Qubits q) (Qubits q) ℂ :=
  Matrix.of fun y x => if y = f x then 1 else 0

/-- A one-qubit matrix on wire `i` of a `q`-wire register, tensored with the identity (the identity
when `i ≥ q`, which `QGate.Valid` excludes). -/
noncomputable def oneQubit {q : ℕ} (M : Matrix Bool Bool ℂ) (i : ℕ) :
    Matrix (Qubits q) (Qubits q) ℂ :=
  if h : i < q then
    embedOp (k := 1) (M.submatrix (fun b => b 0) (fun b => b 0))
      ⟨fun _ => ⟨i, h⟩, fun a b _ => Subsingleton.elim a b⟩
  else 1

/-- The matrix of one gate on `q` wires, the QRAM reading the table `tab`. -/
noncomputable def gateMat (q : ℕ) (tab : List (List Bool)) : QGate → Matrix (Qubits q) (Qubits q) ℂ
  | .H i => oneQubit hadamard i
  | .T i => oneQubit gateT i
  | .CNOT c t => permMat fun z w => if w.val = t then xor (z w) (getb z c) else z w
  | .QRAM a d => permMat (qramMap tab a d)

/-- The unitary of a circuit: the first gate of the list is applied first. -/
noncomputable def circMat (q : ℕ) (tab : List (List Bool)) (C : List QGate) :
    Matrix (Qubits q) (Qubits q) ℂ :=
  C.foldl (fun U g => gateMat q tab g * U) 1

/-- A request of the classical controller: halt with an output, write cell `j` of the QRAM table
(overwrite if `j` is in the table, append if `j` is its length), or run the circuit `C` on `q` wires
from `|0^q⟩` and measure all wires in the computational basis. -/
inductive Req where
  | halt (out : List Bool)
  | write (j : ℕ) (x : List Bool)
  | query (q : ℕ) (C : List QGate)

/-- A list of naturals, self-delimiting. -/
def encNatList (l : List ℕ) : List Bool :=
  encodeNat l.length ++ l.flatMap encodeNat

/-- The self-delimiting encoding of a gate: a two-bit tag, then its wires. -/
def encGate : QGate → List Bool
  | .H i => [false, false] ++ encodeNat i
  | .T i => [false, true] ++ encodeNat i
  | .CNOT c t => [true, false] ++ encodeNat c ++ encodeNat t
  | .QRAM a d => [true, true] ++ encNatList a ++ encNatList d

/-- The encoding of a request, as the controller leaves it on its output stack. -/
def encReq : Req → List Bool
  | .halt out => [false, false] ++ encString out
  | .write j x => [false, true] ++ encodeNat j ++ encString x
  | .query q C => [true, false] ++ encodeNat q ++ encodeNat C.length ++ C.flatMap encGate

/-- Run the controller from `c` until it halts (`c.l = none`), for at most `fuel` steps; return the
number of steps and the halted configuration. -/
def runSeg (tm : Turing.FinTM2) : ℕ → tm.Cfg → Option (ℕ × tm.Cfg)
  | fuel, c =>
    match c.l, fuel with
    | none, _ => some (0, c)
    | some _, 0 => none
    | some _, fuel + 1 =>
      match tm.step c with
      | none => none
      | some c' => (runSeg tm fuel c').map fun p => (p.1 + 1, p.2)

/-- Resume a halted controller after a request: the label returns to `main`, the internal state is
kept, the output stack (the request) is emptied, and the answer `a` is pushed on top of the input
stack; every other stack is kept. -/
def resume (tm : Turing.FinTM2) (c : tm.Cfg) (a : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := some tm.main
  var := c.var
  stk k :=
    (@dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact a)
      fun _ => []) ++
    (@ite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) [] (c.stk k))

/-- `acceptProb M S E r B c tab`: the probability that the hybrid run of `M` from controller
configuration `c` and QRAM table `tab`, within `r` rounds, halts with total cost at most `B`, never
holds more than `S` QRAM cells, and outputs a string satisfying `E`. A round is one controller segment
followed by its request; a query branches on every measurement outcome with its Born probability.
The cost of a round is its controller steps, plus the number of gates of the circuit for a query
(every gate, including each QRAM call, at unit cost). A malformed request (an undecodable output
stack, an invalid gate, a write past the end of the table) ends the branch with value `0`. -/
noncomputable def acceptProb (M : Turing.TM2ComputableAux Bool Bool) (S : ℕ)
    (E : List Bool → Prop) : ℕ → ℕ → M.tm.Cfg → List (List Bool) → ℝ
  | 0, _, _, _ => 0
  | r + 1, B, c, tab =>
    match runSeg M.tm B c with
    | none => 0
    | some (k, c') =>
      if h : ∃ req, encReq req = (c'.stk M.tm.k₁).map M.outputAlphabet then
        match Classical.choose h with
        | .halt out => if E out then 1 else 0
        | .write j x =>
            let tab' := if j < tab.length then tab.set j x else tab ++ [x]
            if j ≤ tab.length ∧ tab'.length ≤ S then
              acceptProb M S E r (B - k) (resume M.tm c' []) tab'
            else 0
        | .query q C =>
            if (∀ g ∈ C, g.Valid q) ∧ k + C.length ≤ B then
              ∑ z : Qubits q,
                prob (act (circMat q tab C) (zeroKet q)) z *
                  acceptProb M S E r (B - k - C.length)
                    (resume M.tm c' ((List.ofFn z).map M.inputAlphabet.invFun)) tab
            else 0
      else 0

/-- `qProb M inp B S E`: the probability that the hybrid quantum–classical machine `M` (§8.1, p.42;
Definition 8.3, p.43), started on input `inp` with an empty QRAM, halts with total cost at most `B`,
QRAM size at most `S` cells, and an output satisfying `E`.

**Formalization Note.**
* *Controller.* A Mathlib TM2 machine over `Bool`, fixed before the input, as in the published
  `RunsWithin`. It issues a request by halting with `encReq req` on its output stack; it is then
  resumed at `main` with its stacks and internal state kept, the request removed and the answer pushed
  on its input stack (the measured bits of a query, nothing for a write). The final output is the
  payload of a `halt` request.
* *Quantum calls.* A query `(q, C)` is a circuit over `{H, T, CNOT}` and QRAM gates on `q` wires; it
  is applied to `|0^q⟩` and all wires are measured, outcome `z` having the Born probability
  `|⟨z|C|0^q⟩|²` (published `QAlgorithms.prob`). A QRAM gate realizes Definition 8.3,
  `|j⟩|b⟩ ↦ |j⟩|b ⊕ x_j⟩`, on the table as it stands; the cells are written classically by `write`
  requests (§8.2, "the cells are written classically and can then be read in superposition").
  Classical coins are obtained by measuring Hadamard states.
* *Cost.* Controller steps plus, for each query, the number of gates (each QRAM call unit cost,
  Definition 8.3). The controller writes every circuit and every cell on its output stack, so their
  description length is charged as well. *QRAM size*: the number of cells of the table, which never
  shrinks, so its final length is its maximum over the run.
* *Rounds.* Every round costs at least one controller step (a resumed controller is not halted), so a
  run of cost at most `B` has at most `B` rounds and the round budget `B + 1` cuts no run.
* With all branches' Born weights summing to `1`, `qProb M inp B S (fun _ => True) = 1` says that every
  branch of positive probability halts within cost `B` and QRAM size `S` (a worst-case bound). -/
noncomputable def qProb (M : Turing.TM2ComputableAux Bool Bool) (inp : List Bool) (B S : ℕ)
    (E : List Bool → Prop) : ℝ :=
  acceptProb M S E (B + 1) B (Turing.initList M.tm (inp.map M.inputAlphabet.invFun)) []

end Supplement

end LIPAlgorithm


