-- Prove2me | Definitions.Def_HeisenbergRep_Knill_singlePauli
-- name    : HeisenbergRep_Knill_singlePauli
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:21.692132+00:00
-- url     : https://prove2.me/theorems/f2c482c3-79df-4c6f-94d4-6654b55f46ae
-- title:
--   The single-qubit Pauli operator $P_q$ on qubit $q$ ($X_q$, $Z_q$)
-- statement:
--   For a qubit $q\in\{0,\dots,n-1\}$ of an $n$-qubit computer and a one-qubit Pauli matrix $P\in\{I,X,Y,Z\}$, the operator $P_q$ is the $n$-qubit Pauli operator with overall phase $+1$ that acts as $P$ on qubit $q$ and as the identity on every other qubit:
--
--   $$P_q=I\otimes\cdots\otimes I\otimes\underbrace{P}_{\text{qubit }q}\otimes I\otimes\cdots\otimes I .$$
--
--   The $2n$ operators $X_q$ and $Z_q$ form the generating set $\{X_1,\dots,X_n,Z_1,\dots,Z_n\}$ of the Pauli group used throughout the paper: the action of a Clifford gate is recorded by its images of these operators.
--
--   **Formalization Note** Qubits are numbered $0,\dots,n-1$ (the paper's qubit $i$ is qubit $i-1$ here); qubit $0$ is the first tensor factor. The operator is a `PauliString n` with phase exponent $0$.
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §2, p. 3 ("The operators X_i, Y_i, and Z_i are X, Y, and Z acting on the ith qubit"), p. 4 (generating set {X_1, …, X_n, Z_1, …, Z_n})

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer

/-- **The single-qubit Pauli operator `P_q` on wire `q`.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §2,
p. 3: "The operators `X_i`, `Y_i`, and `Z_i` are `X`, `Y`, and `Z` acting on the `i`th qubit in the
computer"; p. 4: "A convenient generating set is just `{X_1, …, X_n, Z_1, …, Z_n}`".

`singlePauli q P` is the Pauli string with phase `+1` (phase exponent `0`), the one-qubit Pauli `P`
on wire `q` and the identity `I` on every other wire.

**Formalization Note.** Wires are `Fin n` (the paper's qubit `i` is wire `i − 1`); wire `0` is the
first tensor factor of `PauliString.toMatrix`. -/
def singlePauli {n : ℕ} (q : Fin n) (P : Pauli) : PauliString n :=
  ⟨0, fun r => if r = q then P else .I⟩

end HeisenbergRep.Knill


