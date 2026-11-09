-- Prove2me | Definitions.Def_DepthOneQExp_zMat
-- name    : DepthOneQExp_zMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:29.881417+00:00
-- url     : https://prove2.me/theorems/a2be2f6f-d325-4508-94ed-ae56437f2607
-- title:
--   Pauli $Z$ on qubit $j$
-- statement:
--   The Pauli $Z$ gate on qubit $j$ of an $n$-qubit register is the diagonal matrix
--   $$
--   Z_j\,|x\rangle = (-1)^{x_j}\,|x\rangle .
--   $$
--   For $j$ the first qubit it is $Z\otimes I_{2^{n-1}}$, the gate $U_2$ of Eq. (2.1) and $P_{m+2}$ of Theorem 2.13. The module proves that it is unitary.
--
--   **Formalization Note** 0-based qubit index taken mod $n$; the paper's qubit 1 is $j=0$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.1), p.6; Theorem 2.13, p.11

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_bit

namespace DepthOneQExp

/-- The Pauli `Z` gate on qubit `j` of an `n`-qubit register: the diagonal matrix with entry
`(−1)^{x_j}` at the basis state `|x⟩` (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1
expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Eq. (2.1), p.6, and Theorem 2.13, p.11: `Z ⊗ I_{2^{n−1}}`).

**Formalization Note** 0-based qubit index taken mod `n` (the paper's qubit 1 is `j = 0`). -/
def zMat (n j : ℕ) : Matrix (MITMSynthesis.Q n) (MITMSynthesis.Q n) ℂ :=
  Matrix.diagonal fun x => if bit x j = 1 then -1 else 1

theorem zMat_mem_unitaryGroup (n j : ℕ) : zMat n j ∈ Matrix.unitaryGroup (MITMSynthesis.Q n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext y x
  simp only [zMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp_all

end DepthOneQExp


