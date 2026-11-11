-- Prove2me | Definitions.Def_DepthOptQC_Synth_gToffoli
-- name    : DepthOptQC_Synth_gToffoli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:12:58.513347+00:00
-- url     : https://prove2.me/theorems/05750b19-33b2-4200-9db2-9b2bb3ca7875
-- title:
--   The generalized Toffoli gate with $k$ controls
-- statement:
--   For $k\ge 0$, the **generalized Toffoli gate** with control set $S$ of size $k$ and target qubit $t$ acts on computational basis states by
--   $$
--   |z_S, z_t\rangle \longmapsto |z_S\rangle\,\Big|\,z_t \oplus \prod_{i\in S} z_i\Big\rangle ,
--   $$
--   so the target is flipped exactly when every control is $|1\rangle$. With one control it is CNOT, and with two controls it is the ordinary three-qubit Toffoli gate. Its **width** is its number $k$ of controls.
--
--   **Formalization Note** On $k+1$ gate wires, the controls are wires $0,\dots,k-1$ and the target is wire $k$; the matrix is the permutation matrix of the map above. With $k=0$ the empty product is $1$ and the gate is $X$; the gate sets of the mission use only $k\ge1$.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §1.1, Eq. (3), p.4

import Definitions.Def_QAlgorithms_Defs_Circuit

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The generalized Toffoli matrix with `k` controls** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Eq. (3), p.4): `|z_S, z_t⟩ ↦ |z_S⟩|z_t ⊕ ∏_{i∈S} z_i⟩` on `k + 1`
qubits, with the controls on gate wires `0, …, k−1` and the target on gate wire `k`. It is the
permutation matrix whose `(y, z)` entry is `1` iff `y` is `z` with bit `k` XORed by the AND of
bits `0, …, k−1`.

**Formalization Note.** With `k = 0` the empty AND is `true`, so the gate is `X`; with `k = 1` it is
`CNOT` (control first); with `k = 2` it is the ordinary three-qubit Toffoli. The width of a
generalized Toffoli is its number of controls `k` (reading R5). -/
def gToffoliMat (k : ℕ) : Matrix (Qubits (k + 1)) (Qubits (k + 1)) ℂ :=
  Matrix.of fun y z =>
    if y = Function.update z (Fin.last k)
        (xor (z (Fin.last k)) (decide (∀ i : Fin k, z i.castSucc = true))) then 1 else 0

/-- **The generalized Toffoli gate with `k` controls** (Vasconcelos, arXiv:2609.34659, Eq. (3),
p.4), as a `QAlgorithms.Gate` of arity `k + 1`. `gToffoli 2` is the ordinary Toffoli gate of
Eq. (79), p.23. -/
def gToffoli (k : ℕ) : Gate :=
  ⟨k + 1, gToffoliMat k⟩

end DepthOptQC.Synth


