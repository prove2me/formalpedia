-- Prove2me | Definitions.Def_CompNonlocal_ICirc
-- name    : CompNonlocal_ICirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:08.785207+00:00
-- url     : https://prove2.me/theorems/2bc12aad-4994-473b-8ae6-39c5719377c3
-- title:
--   Quantum circuits with a classical/quantum interface
-- statement:
--   The computational model. A circuit $C$ has $n_c$ classical-input wires, $n_q$ quantum-input wires and $n_a$ ancilla wires, a layered circuit over the gate set $\{H,S,T,X,\mathrm{CNOT}\}$ (each layer acting on disjoint wires), a list of **measured** wires and a disjoint list of **retained** wires. It is run on a classical input string $x$ (on the classical wires, as basis states), an input register (on the quantum wires) and $|0\rangle$ ancillas; at the end the measured wires are read in the computational basis (the classical output, in order), the retained wires are the quantum output, and all other wires are traced out.
--
--   This is the QCCC model of the paper: algorithms are quantum circuits that "may retain quantum states locally, and exchange only classical messages"; "the parties start with independent private workspaces".
--
--   **Formalization Note** The paper fixes no gate set; Clifford+T is universal. A classical input string is read bit by bit and padded with $0$; an $m$-qubit input register feeds the first $\min(m,n_q)$ quantum wires (the others start in $|0\rangle$). The size is the number of instructions, the width the number of wires. Defined with its unitary $U$ ($U_{zy}=\langle z|U|y\rangle$) and the classical output of a full computational-basis outcome.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4, pp.17–18 and §4.4, p.20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- Quantum circuits with a classical/quantum interface, the computational model of Głuch,
Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript
(STOC 2027 submission, sha256 e245edd7…), §4, pp.17–18 ("QPT denotes a uniform quantum
polynomial-time algorithm … adversaries are polynomial-size quantum circuit families with classical
advice") and §4.4, p.20 ("Honest algorithms are uniform QPT, may retain quantum states locally, and
exchange only classical messages. The parties start with independent private workspaces").

A circuit has `nc` classical-input wires, `nq` quantum-input wires and `na` ancilla wires, laid
out in this order on `Fin (nc + nq + na)`. Its gates are a layered Clifford+T circuit (the published
`QAlgorithms.Complexity.Instr`: H, S, T, X, CNOT), each layer acting on disjoint wires. At the end
the wires `outC` are measured in the computational basis (their values, in order, are the classical
output), the wires `outQ` are kept (in order, the quantum output), and every other wire is traced
out.

**Formalization Note** The paper fixes no gate set; Clifford+T is universal (Reading 2). The
derived functions in this module: `width` (number of wires), `size` (number of instructions),
`unitary` (the matrix `U` with `U z y = ⟨z| U |y⟩`), `feed` (the basis input: a classical string
on the classical wires, read bit by bit and padded with `false`; an `m`-qubit register on the
quantum-input wires, its qubit `j` on quantum wire `j` for `j < min(m, nq)`, the remaining quantum
wires set to `|0⟩`; ancillas `|0⟩`) and `clOut` (the classical output string of a computational-basis
outcome `z` of all wires). -/
structure ICirc where
  /-- Number of classical-input wires. -/
  nc : ℕ
  /-- Number of quantum-input wires. -/
  nq : ℕ
  /-- Number of ancilla wires, initialized to `|0⟩`. -/
  na : ℕ
  /-- The layered Clifford+T circuit. -/
  gates : Layered (nc + nq + na)
  /-- Each layer acts on pairwise disjoint wires. -/
  layersOk : ∀ l ∈ gates, LayerOk l
  /-- The measured wires, in output order. -/
  outC : List (Fin (nc + nq + na))
  /-- The retained wires, in output order. -/
  outQ : List (Fin (nc + nq + na))
  /-- No wire is both measured and retained, and none is listed twice. -/
  nodup : (outC ++ outQ).Nodup

namespace ICirc

/-- The number of wires. -/
abbrev width (C : ICirc) : ℕ := C.nc + C.nq + C.na

/-- The size: the total number of instructions. -/
def size (C : ICirc) : ℕ := (C.gates.map List.length).sum

/-- The unitary implemented by the gates: `U z y = ⟨z| U |y⟩`. -/
noncomputable def unitary (C : ICirc) : Matrix (Bits C.width) (Bits C.width) ℂ :=
  Matrix.of fun z y => runLayered C.gates (fun w => if w = y then 1 else 0) z

/-- The basis input: classical string `x` on the classical wires, the `m`-qubit basis state `q`
on the quantum-input wires, ancillas `|0⟩`. -/
def feed (C : ICirc) {m : ℕ} (x : Str) (q : Bits m) : Bits C.width :=
  Fin.append
    (Fin.append (fun i : Fin C.nc => x.getD i false)
      (fun j : Fin C.nq => if h : (j : ℕ) < m then q ⟨j, h⟩ else false))
    (fun _ : Fin C.na => false)

/-- The classical output of the computational-basis outcome `z` of all wires. -/
def clOut (C : ICirc) (z : Bits C.width) : Str := C.outC.map z

end ICirc

end CompNonlocal


