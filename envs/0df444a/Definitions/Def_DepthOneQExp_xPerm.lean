-- Prove2me | Definitions.Def_DepthOneQExp_xPerm
-- name    : DepthOneQExp_xPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:12.074811+00:00
-- url     : https://prove2.me/theorems/853f4d35-34e9-48be-a13d-c848d3b688c3
-- title:
--   Pauli $X$ on qubit $j$ as a permutation of $\{0,1\}^n$
-- statement:
--   The Pauli $X$ gate on qubit $j$ of an $n$-qubit register flips that bit: as a permutation of the computational basis,
--   $$
--   x \mapsto x + e_j \pmod 2 .
--   $$
--   Its matrix $P_{x\mapsto x+e_j}$ is $X\otimes I_{2^{n-1}}$ when $j$ is the first qubit, the gate $U_1$ of Eq. (2.1) and $P_{m+1}$ of Theorem 2.13.
--
--   **Formalization Note** 0-based qubit index taken mod $n$; the paper's qubit 1 is $j=0$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.1), p.6; Theorem 2.13, p.11

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp

/-- The Pauli `X` gate on qubit `j` of an `n`-qubit register, as the permutation `x ↦ x + e_j` of the
computational basis `{0,1}ⁿ` (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on
the unitary group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87,
Eq. (2.1), p.6, and Theorem 2.13, p.11: `X ⊗ I_{2^{n−1}}`).

**Formalization Note** 0-based qubit index taken mod `n` (the paper's qubit 1 is `j = 0`). The
matrix of the gate is `permToMatrix (xPerm n j)`. -/
def xPerm (n j : ℕ) : Equiv.Perm (MITMSynthesis.Q n) :=
  Function.Involutive.toPerm (fun x k => if (k : ℕ) = j % n then x k + 1 else x k) (by
    intro x
    funext k
    by_cases h : (k : ℕ) = j % n
    · simp only [h, if_true]
      generalize x k = c
      revert c
      decide
    · simp [h])

end DepthOneQExp


