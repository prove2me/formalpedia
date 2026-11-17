-- Prove2me | Definitions.Def_GapAgnosticGS_Supplement_oracleSum
-- name    : GapAgnosticGS_Supplement_oracleSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:28:10.660945+00:00
-- url     : https://prove2.me/theorems/79b6e5fc-9474-4354-987f-f6a1e91e50b3
-- title:
--   Two-oracle access as one oracle: the direct sum $U\oplus V$
-- statement:
--   Theorems 1.3, 4.3 and 4.4 give the learner controlled access to two unitaries at once: the evolution oracle $W_H$ (or the hidden-basis environment $E$) and a state-preparation unitary $U_0$ (or $U_I$), together with their inverses, and they count the queries to both. For unitaries $U$ on $\mathbb C^{Q_1}$ and $V$ on $\mathbb C^{Q_2}$ the **direct-sum oracle** is the block-diagonal unitary
--
--   $$
--   U\oplus V=\begin{pmatrix}U&0\\0&V\end{pmatrix}\quad\text{on } \mathbb C^{Q_1}\oplus\mathbb C^{Q_2}.
--   $$
--
--   A controlled query to $U\oplus V$ is simulated by one controlled query to each of $U$ and $V$, and a controlled query to $U$ (or to $V$) is one controlled query to $U\oplus V$ with the oracle register prepared in the corresponding block. Hence "$O(X)$ queries to $U$ and the same order of queries to $V$" is the same requirement as "$O(X)$ queries to $U\oplus V$", which lets the single-oracle algorithm model of the base mission count two-oracle access.
--
--   **Formalization Note** `Matrix.fromBlocks U 0 0 V`, indexed by the sum type `Q₁ ⊕ Q₂`.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §4, (7) and Problem 4.1, p.17 (PDF p.18); Theorem 1.3, p.3 (PDF p.4)

import Mathlib

namespace GapAgnosticGS.Supplement

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §4, p.17 (PDF p.18), (7) and Problem 4.1: "controlled access to a HidQMAB environment E
and its inverse E†, and controlled access to a unitary U_I and its inverse U_I†"; Theorem 1.3,
p.3 (PDF p.4): access to `W_H` and to a unitary preparing `|ψ_0⟩`. The **two-oracle access** of
Theorems 1.3, 4.3 and 4.4, as one oracle: the block-diagonal direct sum `U ⊕ V` on `Q₁ ⊕ Q₂`,
`(U ⊕ V)(q₁) = U q₁`, `(U ⊕ V)(q₂) = V q₂`.

**Formalization Note.** One controlled query to `U ⊕ V` costs one controlled query to each of
`U` and `V`, and one controlled query to `U` (or `V`) is one controlled query to `U ⊕ V` with
the oracle register in the corresponding block. So "`O(X)` queries to `U` and the same order of
queries to `V`" is the same as "`O(X)` queries to `U ⊕ V`". For unitary `U`, `V` the sum is
unitary. -/
def oracleSum {Q₁ Q₂ : Type} (U : Matrix Q₁ Q₁ ℂ) (V : Matrix Q₂ Q₂ ℂ) :
    Matrix (Q₁ ⊕ Q₂) (Q₁ ⊕ Q₂) ℂ :=
  Matrix.fromBlocks U 0 0 V

end GapAgnosticGS.Supplement


