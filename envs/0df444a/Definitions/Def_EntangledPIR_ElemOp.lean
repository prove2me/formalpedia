-- Prove2me | Definitions.Def_EntangledPIR_ElemOp
-- name    : EntangledPIR_ElemOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:54.632201+00:00
-- url     : https://prove2.me/theorems/f48b51fa-f19a-4225-94ef-38fe6e624587
-- title:
--   Elementary operations and their semantics
-- statement:
--   On a set $Q$ of qubits with basis states $Q\to\{0,1\}$ and a classical memory, the elementary operations are: the reversible gates Pauli X, CNOT and Toffoli, which permute basis states; the Hadamard gate; the measurement of one qubit in the computational basis, with its outcome written to a memory cell; and a classical bit operation. Each may be under classical control of a memory cell. The run of a list on measurement outcomes gives a product of Kraus operators and a final memory.
--
--   **Formalization Note** Gate qubits are distinct, so every gate is unitary. Every operation has outcome bit false except an active measurement, which has both, so the sum over outcome lists is complete.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 5.4(iii), p.27; Claim C.3, p.57; proof pp.57–58

import Definitions.Def_EntangledPIR_table
import Definitions.Def_EntangledPIR_testProj

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Claim C.3,
p.57; Lemma 5.4(iii), p.27: elementary operations.
-/

open Matrix

namespace EntangledPIR

/-- The reversible gates of Claim C.3, p.57, on a set `Q` of qubits: Pauli X, CNOT and Toffoli. The
qubits of a gate are distinct, so each gate is a permutation of the basis states. -/
inductive RevGate (Q : Type)
  | x (q : Q)
  | cnot (c t : Q) (h : c ≠ t)
  | toffoli (c₁ c₂ t : Q) (h₁ : c₁ ≠ c₂) (h₂ : c₁ ≠ t) (h₃ : c₂ ≠ t)

variable {Q : Type} [DecidableEq Q]

/-- The action of a reversible gate on basis states `Q → Bool`. -/
def RevGate.apply : RevGate Q → (Q → Bool) → (Q → Bool)
  | .x q, s => Function.update s q (!s q)
  | .cnot c t _, s => if s c then Function.update s t (!s t) else s
  | .toffoli c₁ c₂ t _ _ _, s => if s c₁ && s c₂ then Function.update s t (!s t) else s

/-- The action of a list of reversible gates on basis states, in order. -/
def runGates (gs : List (RevGate Q)) (s : Q → Bool) : Q → Bool :=
  gs.foldl (fun s g => g.apply s) s

/-- The unitary of a reversible gate: the permutation matrix of `RevGate.apply`. -/
def RevGate.matrix (g : RevGate Q) [Fintype Q] : Matrix (Q → Bool) (Q → Bool) ℂ :=
  Matrix.of fun s s' => if s = g.apply s' then 1 else 0

/-- The Hadamard gate on qubit `q`: `2^{-1/2} (-1)^{s_q s'_q}` between basis states that agree
off `q`. -/
noncomputable def hadamardMatrix [Fintype Q] (q : Q) : Matrix (Q → Bool) (Q → Bool) ℂ :=
  Matrix.of fun s s' =>
    if ∀ q', q' ≠ q → s q' = s' q' then
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if s q && s' q then -1 else 1)
    else 0

/-- The projector of outcome `b` of the measurement of qubit `q` in the computational basis. -/
def measMatrix [Fintype Q] (q : Q) (b : Bool) : Matrix (Q → Bool) (Q → Bool) ℂ :=
  Matrix.diagonal fun s => if s q = b then 1 else 0

/-- A classical bit operation: `mem dst := f (mem a) (mem b)`, for any Boolean function `f` of two bits,
on a classical memory with cells `C`. -/
structure BitOp (C : Type) where
  /-- the Boolean function -/
  f : Bool → Bool → Bool
  /-- first input cell -/
  a : C
  /-- second input cell -/
  b : C
  /-- output cell -/
  dst : C

variable {C : Type} [DecidableEq C]

/-- The action of a classical bit operation on the memory. -/
def BitOp.apply (op : BitOp C) (mem : C → Bool) : C → Bool :=
  Function.update mem op.dst (op.f (mem op.a) (mem op.b))

/-- The action of a list of bit operations on the memory, in order. -/
def runBits (ops : List (BitOp C)) (mem : C → Bool) : C → Bool :=
  ops.foldl (fun mem op => op.apply mem) mem

/-- The elementary operations of Lemma 5.4(iii), p.27: a Hadamard, Pauli X, CNOT, or Toffoli gate, a
measurement of one qubit in the computational basis (its outcome written to a memory cell), or a
classical bit operation. -/
inductive ElemOpKind (Q C : Type)
  | gate (g : RevGate Q)
  | hadamard (q : Q)
  | meas (q : Q) (dst : C)
  | bit (op : BitOp C)

/-- An elementary operation, possibly under classical control of a memory cell (A.1, p.53, "classical
control"; Claim C.3's NOT gates act according to the value `g(q₀ ⊕ z)`). It is skipped if the cell holds
`false`. -/
structure ElemOp (Q C : Type) where
  /-- the control cell, if any -/
  ctrl : Option C
  /-- the operation -/
  op : ElemOpKind Q C

/-- Whether the control of the operation allows it. -/
def ElemOp.active {Q : Type} (o : ElemOp Q C) (mem : C → Bool) : Bool :=
  match o.ctrl with
  | none => true
  | some c => mem c

/-- The Kraus operator of one operation for measurement outcome `b`: only an active measurement has two
outcomes; every other operation has the outcome `false` only. -/
noncomputable def ElemOp.kraus [Fintype Q] (o : ElemOp Q C) (mem : C → Bool) (b : Bool) :
    Matrix (Q → Bool) (Q → Bool) ℂ :=
  if o.active mem then
    match o.op with
    | .gate g => if b then 0 else g.matrix
    | .hadamard q => if b then 0 else hadamardMatrix q
    | .meas q _ => measMatrix q b
    | .bit _ => if b then 0 else 1
  else if b then 0 else 1

/-- The memory after one operation for measurement outcome `b`. -/
def ElemOp.nextMem {Q : Type} (o : ElemOp Q C) (mem : C → Bool) (b : Bool) : C → Bool :=
  if o.active mem then
    match o.op with
    | .meas _ dst => Function.update mem dst b
    | .bit op => op.apply mem
    | _ => mem
  else mem

/-- The run of a list of operations from the memory `mem`, with measurement outcomes `ω`, one per
operation: the product of its Kraus operators, last operation first, and the final memory. -/
noncomputable def runProg [Fintype Q] : List (ElemOp Q C) → List Bool → (C → Bool) →
    Matrix (Q → Bool) (Q → Bool) ℂ × (C → Bool)
  | [], _, mem => (1, mem)
  | o :: os, ω, mem =>
    let b := ω.headD false
    let rest := runProg os ω.tail (o.nextMem mem b)
    (rest.1 * o.kraus mem b, rest.2)

end EntangledPIR


