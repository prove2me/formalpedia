-- Prove2me | Definitions.Def_WildeQIT_Hashing_IsStabilizerCode
-- name    : WildeQIT_Hashing_IsStabilizerCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:20:54.296123+00:00
-- url     : https://prove2.me/theorems/0eb4a140-c804-465f-945a-026ef5d4e8e6
-- title:
--   $[n,k]$ stabilizer code: an abelian subgroup of $G_n$ of size $2^{n-k}$ without $-I$
-- statement:
--   Let $G_n=\{\pm1,\pm i\}\otimes\{I,X,Y,Z\}^{\otimes n}$ be the Pauli group on $n$ qubits. A subgroup $\mathcal S\subseteq G_n$ is an **$[n,k]$ stabilizer code** when
--
--   1. $\mathcal S$ is abelian and $-I\notin\mathcal S$;
--   2. $0\le k\le n$ and $|\mathcal S|=2^{n-k}$.
--
--   Its codespace is the subspace $\{|\psi\rangle : S|\psi\rangle=|\psi\rangle\ \forall S\in\mathcal S\}$ of the $2^n$-dimensional space of $n$ qubits; it has dimension $2^k$, so the code encodes $k$ logical qubits into $n$ physical qubits.
--
--   This is the class of codes over which the hashing bound (Theorem 24.6.2) is an existence statement.
--
--   **Formalization Note** $\mathcal S$ is a subgroup of Mathlib's unitary group on `Qubits n` (`Fin n → Bool`); "abelian subgroup of the Pauli group without $-I$" is the published predicate `QAlgorithms.IsStabilizerGroup`. The book does not write $-I\notin\mathcal S$; it follows from its statement that the codespace has dimension $2^k\ge1$, since a group containing $-I$ stabilizes only the zero vector.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.6.2, p. 673, (24.95)–(24.96)

import Definitions.Def_QAlgorithms_Defs_QECC

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.6.2, p. 673
(an `[n, k]` stabilizer code).
-/

namespace WildeQIT.Hashing

open QAlgorithms

/-- **An `[n, k]` stabilizer code** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §24.6.2, p. 673): `S` is an abelian subgroup of the `n`-qubit Pauli group
`Gₙ = {±1, ±i} ⊗ {I, X, Y, Z}^{⊗n}` (24.95) of size `2^{n−k}`, with `0 ≤ k ≤ n`; its codespace,
"the `2^k`-dimensional subspace … stabilized by `S`" (24.96), encodes `k` logical qubits into `n`
physical qubits.

**Formalization Note.** `S` is a subgroup of Mathlib's unitary group `U(2ⁿ)` on `Qubits n`
(`Fin n → Bool`), and `IsStabilizerGroup S` is the published predicate "abelian subgroup of the
Pauli group not containing `−I`". The book does not write `−I ∉ S`, but it is implied by its
claim that the codespace has dimension `2^k ≥ 1` (an `S` containing `−I` stabilizes only `0`).
The size is `Nat.card S`. -/
def IsStabilizerCode (n k : ℕ) (S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ)) : Prop :=
  IsStabilizerGroup S ∧ k ≤ n ∧ Nat.card S = 2 ^ (n - k)

end WildeQIT.Hashing


