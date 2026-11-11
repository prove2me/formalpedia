-- Prove2me | Definitions.Def_DepthOptQC_Synth_fanOut
-- name    : DepthOptQC_Synth_fanOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:11.936559+00:00
-- url     : https://prove2.me/theorems/516b592b-881e-4d08-9727-7d40e2a33a4d
-- title:
--   The Fan-Out gate with $k$ targets
-- statement:
--   For $k\ge 1$, the **Fan-Out gate** with control qubit $c$ and target set $S$ of size $k$ acts on computational basis states by
--   $$
--   |z_c\rangle\,|z_S\rangle \longmapsto |z_c\rangle\,|z_S \oplus z_c\mathbf 1\rangle ,
--   $$
--   so the value of the control is XORed into every target. With one target it is CNOT. Its **width** is its number $k$ of targets.
--
--   **Formalization Note** On $k+1$ gate wires, the control is wire $0$ and the targets are wires $1,\dots,k$; the matrix is the permutation matrix of the map above.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §1.1, Eq. (5), p.4; p.19 (a CNOT is a Fan-Out gate with one target)

import Definitions.Def_QAlgorithms_Defs_Circuit

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The Fan-Out matrix with `k` targets** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Eq. (5), p.4): `|z_c⟩|z_S⟩ ↦ |z_c⟩|z_S ⊕ z_c 1⟩` on `k + 1` qubits, with the
control on gate wire `0` and the targets on gate wires `1, …, k`. It is the permutation matrix whose
`(y, z)` entry is `1` iff `y 0 = z 0` and `y j = z j ⊕ z 0` for every `j ≥ 1`.

**Formalization Note.** The width of a Fan-Out gate is its number of targets `k` (reading R5;
Lemma 4, p.18: "Fan-Out gates with at most `b_max` targets"). With `k = 1` it is `CNOT` (p.19: "a
CNOT is a Fan-Out gate with one target"). -/
def fanOutMat (k : ℕ) : Matrix (Qubits (k + 1)) (Qubits (k + 1)) ℂ :=
  Matrix.of fun y z =>
    if y = (fun j : Fin (k + 1) => if j = 0 then z 0 else xor (z j) (z 0)) then 1 else 0

/-- **The Fan-Out gate with `k` targets** (Vasconcelos, arXiv:2609.34659, Eq. (5), p.4), as a
`QAlgorithms.Gate` of arity `k + 1`. -/
def fanOut (k : ℕ) : Gate :=
  ⟨k + 1, fanOutMat k⟩

end DepthOptQC.Synth


