-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_qubitOp
-- name    : HeilmanMax3Cut_Supplement_qubitOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:00.275185+00:00
-- url     : https://prove2.me/theorems/88662953-7e66-4f53-ba45-123cffd9dc48
-- title:
--   A one-qubit operator on the $j$-th tensor factor
-- statement:
--   For a $2\times2$ complex matrix $P$ and $1\le j\le n$, the operator $P_j=I_2^{\otimes(j-1)}\otimes P\otimes I_2^{\otimes(n-j)}$ on $(\mathbb C^2)^{\otimes n}$. With $P$ the Pauli matrices
--
--   $$X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Y=\begin{pmatrix}0&-\sqrt{-1}\\ \sqrt{-1}&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$$
--
--   this gives the operators $X_j,Y_j,Z_j$ of the Quantum MAX-CUT Hamiltonian.
--
--   **Formalization Note** $(\mathbb C^2)^{\otimes n}$ is the space of functions on bit strings $b\in\{0,1\}^n$; the entry at $(b,b')$ is $P_{b_j b'_j}$ when $b$ and $b'$ agree off $j$ and $0$ otherwise. Qubits are indexed $0,\dots,n-1$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 2.1, p.10

import Mathlib

namespace HeilmanMax3Cut.Supplement

/-- **A one-qubit operator acting on the `j`-th tensor factor.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 2.1, p.10:
`Z_j := I₂^{⊗(j−1)} ⊗ [[1, 0], [0, −1]] ⊗ I₂^{⊗(n−j)}`, and likewise `X_j`, `Y_j` with the matrices
`[[0, 1], [1, 0]]` and `[[0, −√−1], [√−1, 0]]`.

`qubitOp P j` is `I₂^{⊗(j−1)} ⊗ P ⊗ I₂^{⊗(n−j)}` for a `2 × 2` matrix `P`.

**Formalization Note.** `(ℂ²)^{⊗n}` is realised as `(Fin n → Fin 2) → ℂ` with the computational basis
indexed by bit strings `b : Fin n → Fin 2`; the qubits `1, …, n` are `0, …, n − 1`. The matrix entry
at `(b, b')` is `P (b j) (b' j)` if `b` and `b'` agree off `j`, and `0` otherwise, which is the
Kronecker product with identities on the other factors. -/
def qubitOp {n : ℕ} (P : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin n) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun b b' => if ∀ l, l ≠ j → b l = b' l then P (b j) (b' j) else 0

end HeilmanMax3Cut.Supplement


