-- Prove2me | Definitions.Def_BaconThesis_WeakUniv_exchange
-- name    : BaconThesis_WeakUniv_exchange
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:40.744085+00:00
-- url     : https://prove2.me/theorems/a7181cdf-f83c-409d-94f5-ca483f55eef8
-- title:
--   Eq. (9.8) — the exchange interaction $E_{ij}$
-- statement:
--   The **exchange interaction** on two qubits is the operator
--   $$
--   E=\begin{pmatrix} 1&0&0&0\\ 0&0&1&0\\ 0&1&0&0\\ 0&0&0&1\end{pmatrix}=\tfrac12\big(I+\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y+\sigma_z\otimes\sigma_z\big)
--   $$
--   in the computational basis $|00\rangle,|01\rangle,|10\rangle,|11\rangle$. It swaps the two qubits: $E|\psi\rangle|\varphi\rangle=|\varphi\rangle|\psi\rangle$.
--
--   It is one of the four nearest-neighbour generators whose Lie algebra the mission studies.
--
--   **Formalization Note** The matrix is written in the basis $|ab\rangle\leftrightarrow(a,b)$, row order $2a+b$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §9.1.2, eq. (9.8), p.126 (PDF p.143)

import Mathlib

namespace BaconThesis.WeakUniv

/-- **The exchange interaction `E_ij` on two qubits.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§9.1.2, eq. (9.8), p.126 (PDF p.143): "E_ij = [[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]]
= ½(I + σ_x^{(i)}σ_x^{(j)} + σ_y^{(i)}σ_y^{(j)} + σ_z^{(i)}σ_z^{(j)}) … The exchange operator E_ij
exchanges qubits i and j: E_ij|ψ⟩_i|φ⟩_j = |φ⟩_i|ψ⟩_j."

`exchange` is the matrix of (9.8) in the computational basis `|00⟩, |01⟩, |10⟩, |11⟩`: it fixes
`|00⟩` and `|11⟩` and swaps `|01⟩` and `|10⟩`.

**Formalization Note.** As for `Tmat`, the basis state `|ab⟩` is the pair `(a, b)`, first qubit
first, and the row order is `finProdFinEquiv (a, b) = 2a + b`. -/
def exchange : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (!![1, 0, 0, 0;
      0, 0, 1, 0;
      0, 1, 0, 0;
      0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℂ).submatrix finProdFinEquiv finProdFinEquiv

end BaconThesis.WeakUniv


