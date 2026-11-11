-- Prove2me | Definitions.Def_StabTestMem_weyl
-- name    : StabTestMem_weyl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:26.157128+00:00
-- url     : https://prove2.me/theorems/07e1d1ab-e502-4ba8-a3ce-db8ec0352326
-- title:
--   Hermitian Weyl operator $P_{x,z}=i^{x\cdot z}X^xZ^z$
-- statement:
--   For a label $u=(x,z)\in\mathbb F_2^{2n}$, the **Weyl operator** (Hermitian Pauli operator) is
--
--   $$P_{x,z}=i^{x\cdot z}\,X^{x}Z^{z},$$
--
--   where $X^x=\bigotimes_j X^{x_j}$, $Z^z=\bigotimes_j Z^{z_j}$ and $x\cdot z=\sum_j x_jz_j$ is computed as an **integer**. In the computational basis, $X^xZ^z|y\rangle=(-1)^{z\cdot y}|y\oplus x\rangle$, so the matrix entry in row $y'$ and column $y$ is $i^{x\cdot z}(-1)^{z\cdot y}$ if $y'=y\oplus x$ and $0$ otherwise.
--
--   On one qubit the labels $(1,0)$, $(0,1)$, $(1,1)$ give $X$, $Z$ and $Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$. These operators are Hermitian, square to the identity, and form an orthogonal basis of the $n$-qubit operators.
--
--   **Formalization Note** A label is the published `CutRankSched.Pauli n` (a pair of vectors `Fin n → ZMod 2`, X-part first). Basis strings are `Qubits n = Fin n → Bool` (`false` $=|0\rangle$). The exponent of $i$ is the natural number $\sum_j x_j z_j$ (since $i$ has order $4$ it is not reduced mod $2$); the sign $(-1)^{z\cdot y}$ is computed in $\mathbb F_2$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §2.1, p. 12 (P_{x,z} := i^{x·z} X^x Z^z) and p. 13 (integer inner products)

import Definitions.Def_CutRankSched_Pauli
import Definitions.Def_QAlgorithms_Defs_Basic

namespace StabTestMem

open QAlgorithms

/-- **Hermitian Weyl (Pauli) operator `P_{x,z} = i^{x·z} X^x Z^z`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §2.1, p. 12:
"use the Hermitian Pauli convention P_{x,z} := i^{x·z} X^x Z^z"; the inner products are integer
valued (p. 13, after Eq. (10)).

Its matrix entry in row `y'`, column `y` (computational basis of `n` qubits) is
`i^{x·z} (−1)^{z·y}` if `y' = y ⊕ x` and `0` otherwise, since `X^x Z^z |y⟩ = (−1)^{z·y} |y ⊕ x⟩`.

**Formalization Note.** A label is the published `CutRankSched.Pauli n = (Fin n → ZMod 2) ×
(Fin n → ZMod 2)` (X-part, Z-part; the paper's `(x, z) ∈ F_2^n × F_2^n`, p. 12). `Qubits n = Fin n → Bool` with `false = |0⟩`; a basis string `y` is read
as the `F₂`-vector `j ↦ [y j]`. The exponent `x·z` of `i` is the **integer** inner product
`∑ j, (x j).val * (z j).val` (a natural number; `i` has order 4, so it cannot be reduced mod 2).
The sign `(−1)^{z·y}` only depends on `z·y` mod 2, computed in `ZMod 2`. On one qubit this gives
`X`, `Z` and `Y = [[0, −i], [i, 0]]` for the labels `(1,0)`, `(0,1)`, `(1,1)`. -/
noncomputable def weyl {n : ℕ} (u : CutRankSched.Pauli n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y' y =>
    if (fun j => if y' j then (1 : ZMod 2) else 0) =
        (fun j => (if y j then (1 : ZMod 2) else 0) + u.1 j) then
      Complex.I ^ (∑ j, (u.1 j).val * (u.2 j).val) *
        (-1 : ℂ) ^ (∑ j, u.2 j * (if y j then (1 : ZMod 2) else 0)).val
    else 0

end StabTestMem


