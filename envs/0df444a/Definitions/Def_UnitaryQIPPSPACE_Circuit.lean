-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Circuit
-- name    : UnitaryQIPPSPACE_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:37.178837+00:00
-- url     : https://prove2.me/theorems/43434341-5416-4112-b005-e0b5e41f15c3
-- title:
--   Quantum circuits with initialization, partial trace, gates and measurement
-- statement:
--   A **quantum circuit** is a finite sequence of operations, each of which is the initialization of a new qubit in $|0\rangle$, the partial trace over a qubit, a gate from $\{H,T,\mathrm{CNOT}\}$, or a measurement of a qubit in the computational basis. The qubits present at each step are numbered $0,\dots,k-1$: initialization appends a qubit, a partial trace removes one, and a measurement keeps its outcome as a classical bit in the measured qubit (the dephasing channel $\rho\mapsto\sum_b|b\rangle\langle b|_i\rho|b\rangle\langle b|_i$).
--
--   A circuit is **well formed** from $k$ to $k'$ qubits if every operation names existing (and, for CNOT, distinct) qubits and the circuit ends with $k'$ qubits. Such a circuit is identified with the channel it implements, $\mathcal L(\mathbb C^{2^k})\to\mathcal L(\mathbb C^{2^{k'}})$. Its **size** is its number of operations and it **uses space** $s$ if at most $s$ qubits are present at every step. A **unitary circuit** contains only gates; it has a unitary matrix. The **description** of a circuit is the sequence of the codes of its operations.
--
--   These are the circuits of both synthesis classes and of the verifiers.
--
--   **Formalization Note** Qubit indices are natural numbers checked against the current register size; the channel of a circuit that is not well formed is never used.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2, Quantum circuits, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_Bits
import Definitions.Def_UnitaryQIPPSPACE_embed1
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- An **operation of a quantum circuit** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §2 Quantum circuits, p. 10 (PDF p. 12)): "A
quantum circuit is a finite sequence of operations, each of which is either the initialization of
a new qubit in the state `|0⟩`, the partial trace over a qubit, a unitary gate from `G`, or a
measurement of a qubit in the computational basis", with the gate set `G = {H, T, CNOT}` (p. 9).

Qubits are numbered `0, 1, …, k-1` in the current register of `k` qubits:
* `init` appends a new qubit in `|0⟩` as qubit `k`;
* `discard i` traces out qubit `i` (the later qubits move down by one);
* `hadamard i`, `tgate i` apply `H`, `T` to qubit `i`; `cnot i j` applies `CNOT` with control `i`
  and target `j`;
* `measure i` measures qubit `i` in the computational basis; the outcome stays in qubit `i` as a
  classical bit (the dephasing channel `ρ ↦ ∑_b |b⟩⟨b|_i ρ |b⟩⟨b|_i`).

**Formalization Note** The paper fixes `G` "without loss of generality, … for example,
`{H, T, CNOT}`"; this formalization fixes exactly that set. -/
inductive Op where
  | init
  | discard (i : ℕ)
  | hadamard (i : ℕ)
  | tgate (i : ℕ)
  | cnot (i j : ℕ)
  | measure (i : ℕ)

/-- A **quantum circuit**: the finite sequence of its operations, applied first to last (p. 10). -/
abbrev Circuit : Type := List Op

namespace Op

/-- The number of qubits after the operation, starting from `k` qubits. -/
def next : Op → ℕ → ℕ
  | init, k => k + 1
  | discard _, k => Nat.pred k
  | hadamard _, k => k
  | tgate _, k => k
  | cnot _ _, k => k
  | measure _, k => k

/-- The operation is well formed on a register of `k` qubits: every qubit it names exists, and the
two qubits of a `CNOT` are distinct. -/
def Valid : Op → ℕ → Prop
  | init, _ => True
  | discard i, k => i < k
  | hadamard i, k => i < k
  | tgate i, k => i < k
  | cnot i j, k => i < k ∧ j < k ∧ i ≠ j
  | measure i, k => i < k

/-- The operation is a unitary gate from `G`. -/
def IsGate : Op → Prop
  | hadamard _ => True
  | tgate _ => True
  | cnot _ _ => True
  | _ => False

/-- Initialization: `ρ ↦ ρ ⊗ |0⟩⟨0|`, the new qubit last. -/
def initAct (k : ℕ) (ρ : Matrix (Bits k) (Bits k) ℂ) : Matrix (Bits (k + 1)) (Bits (k + 1)) ℂ :=
  fun x y => if x (Fin.last k) = false ∧ y (Fin.last k) = false then ρ (Fin.init x) (Fin.init y)
    else 0

/-- Partial trace over qubit `i`: `(tr_i ρ)(x, y) = ∑_b ρ(x with b inserted at i, y with b inserted
at i)`. -/
def discardAct (i : ℕ) : (k : ℕ) → Matrix (Bits k) (Bits k) ℂ →
    Matrix (Bits (Nat.pred k)) (Bits (Nat.pred k)) ℂ
  | 0, _ => 0
  | k + 1, ρ => fun x y => if h : i < k + 1 then
      ∑ b : Bool, ρ (Fin.insertNth (α := fun _ => Bool) ⟨i, h⟩ b x)
        (Fin.insertNth (α := fun _ => Bool) ⟨i, h⟩ b y) else 0

/-- Computational-basis measurement of qubit `i` (outcome kept as a classical bit):
`ρ ↦ ∑_b |b⟩⟨b|_i ρ |b⟩⟨b|_i`, i.e. the entries with `x_i ≠ y_i` are erased. -/
def measureAct (i k : ℕ) (ρ : Matrix (Bits k) (Bits k) ℂ) : Matrix (Bits k) (Bits k) ℂ :=
  fun x y => if h : i < k then (if x ⟨i, h⟩ = y ⟨i, h⟩ then ρ x y else 0) else ρ x y

/-- The action of an operation on a `k`-qubit operator (the channel it implements). -/
noncomputable def act : (o : Op) → (k : ℕ) → Matrix (Bits k) (Bits k) ℂ →
    Matrix (Bits (o.next k)) (Bits (o.next k)) ℂ
  | init, k, ρ => initAct k ρ
  | discard i, k, ρ => discardAct i k ρ
  | hadamard i, k, ρ => conjBy (embed1 gateH k i) ρ
  | tgate i, k, ρ => conjBy (embed1 gateT k i) ρ
  | cnot i j, k, ρ => conjBy (embed2 gateCNOT k i j) ρ
  | measure i, k, ρ => measureAct i k ρ

/-- The matrix of a gate on `k` qubits (the identity for a non-gate operation). -/
noncomputable def gateMat : Op → (k : ℕ) → Matrix (Bits k) (Bits k) ℂ
  | hadamard i, k => embed1 gateH k i
  | tgate i, k => embed1 gateT k i
  | cnot i j, k => embed2 gateCNOT k i j
  | _, _ => 1

/-- The **description** of an operation as a bit string: a tag `1^r` (`r = 0, …, 5`) followed by
the binary codes of the qubits it acts on, joined by the tuple encoding `tup`. Distinct operations
have distinct, nonempty codes. -/
def code : Op → Str
  | init => tup [List.replicate 0 true]
  | discard i => tup [List.replicate 1 true, natCode i]
  | hadamard i => tup [List.replicate 2 true, natCode i]
  | tgate i => tup [List.replicate 3 true, natCode i]
  | cnot i j => tup [List.replicate 4 true, natCode i, natCode j]
  | measure i => tup [List.replicate 5 true, natCode i]

end Op

namespace Circuit

/-- The number of qubits at the end of the circuit, starting from `k` qubits. -/
def next : Circuit → ℕ → ℕ
  | [], k => k
  | o :: c, k => next c (o.next k)

/-- Every operation is well formed on the register it meets. -/
def Valid : Circuit → ℕ → Prop
  | [], _ => True
  | o :: c, k => o.Valid k ∧ Valid c (o.next k)

/-- The circuit is well formed with `k` input qubits and `k'` output qubits. -/
def WF (c : Circuit) (k k' : ℕ) : Prop :=
  c.Valid k ∧ c.next k = k'

/-- The action of the circuit on a `k`-qubit operator. -/
noncomputable def act : (c : Circuit) → (k : ℕ) → Matrix (Bits k) (Bits k) ℂ →
    Matrix (Bits (c.next k)) (Bits (c.next k)) ℂ
  | [], _, ρ => ρ
  | o :: c, k, ρ => act c (o.next k) (o.act k ρ)

/-- **The channel implemented by the circuit** from `k` to `k'` qubits ("We identify a quantum
circuit `C` with the quantum channel it implements", p. 10). It is the action of the circuit when
the circuit ends with `k'` qubits, and `0` otherwise (such a circuit is not well formed for
`(k, k')` and is never used). -/
noncomputable def chan (c : Circuit) (k k' : ℕ) (ρ : Matrix (Bits k) (Bits k) ℂ) :
    Matrix (Bits k') (Bits k') ℂ :=
  if h : c.next k = k' then
    cast (congrArg (fun r => Matrix (Bits r) (Bits r) ℂ) h) (c.act k ρ)
  else 0

/-- **Space** of the circuit on `k` input qubits: the largest number of qubits present at any step
("We say that a quantum circuit uses space `s` if the number of qubits involved at every step of
the computation is at most `s`", p. 10). -/
def space : Circuit → ℕ → ℕ
  | [], k => k
  | o :: c, k => max k (space c (o.next k))

/-- A **unitary circuit**: "a quantum circuit that contains only unitary gates" (p. 10). -/
def IsUnitary (c : Circuit) : Prop := ∀ o ∈ c, o.IsGate

/-- The unitary matrix of a unitary circuit on `k` qubits (the ordered product of its gates, the
first gate rightmost). -/
noncomputable def umat (c : Circuit) (k : ℕ) : Matrix (Bits k) (Bits k) ℂ :=
  c.foldl (fun M o => o.gateMat k * M) 1

/-- The **description** of the circuit: "the sequence of its operations together with a
specification of the qubits on which each operation acts" (p. 10), the codes of its operations
joined by `tup`. Its **size** "is the number of operations in its description", `c.length`. -/
def code (c : Circuit) : Str := tup (c.map Op.code)

end Circuit

end UnitaryQIPPSPACE


