-- Prove2me | Definitions.Def_GapAgnosticGS_Supplement_descEigenvalues
-- name    : GapAgnosticGS_Supplement_descEigenvalues
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:30:18.521451+00:00
-- url     : https://prove2.me/theorems/a05cb5f2-9349-431b-bed9-4fb494c15e8e
-- title:
--   Eigenvalues in decreasing order, $\lambda_1\ge\cdots\ge\lambda_n$
-- statement:
--   For a Hermitian $n\times n$ matrix $M$, write its eigenvalues, counted with multiplicity, in **decreasing** order,
--
--   $$
--   \lambda_1\ge\lambda_2\ge\cdots\ge\lambda_n .
--   $$
--
--   This is the ordering used in Section 5: for the transition matrix of a reversible chain (through its symmetric discriminant), $1=\lambda_1>\lambda_2\ge\cdots\ge\lambda_n\ge0$ (Theorem 5.1), and for the block $D_U$ of a Hermitian unitary, $1=\lambda_1=\cdots=\lambda_r>\lambda_{r+1}\ge\cdots\ge\lambda_n\ge0$ (Theorem 5.4).
--
--   **Formalization Note** Indices are 0-based: the Lean value at index $j$ is the paper's $\lambda_{j+1}$. It is the published `QAlgorithms.ascEigenvalues` read in reverse; for a non-Hermitian matrix the value is $0$, and every statement applies it to a Hermitian matrix.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 5.1, p.23 (PDF p.24); Theorem 5.4, p.24 (PDF p.25)

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
open QAlgorithms

namespace GapAgnosticGS.Supplement

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 5.1, p.23 (PDF p.24): "Write its eigenvalues as 1 = λ_1 > λ_2 ≥ ⋯ ≥ λ_n ≥ 0";
Theorem 5.4, p.24 (PDF p.25): "D_U has eigenvalues 1 = λ_1 = ⋯ = λ_r > λ_{r+1} ≥ ⋯ ≥ λ_n ≥ 0".
The eigenvalues of an `n × n` matrix, counted with multiplicity, in **decreasing** order:
`descEigenvalues M j` is the paper's `λ_{j+1}`.

**Formalization Note.** Indices are 0-based (`j = 0` is the largest eigenvalue `λ_1`). This is the
published `QAlgorithms.ascEigenvalues M` read backwards (`Fin.rev`), re-indexed by `Fin n`. For a
non-Hermitian matrix the value is `0`; every statement using it applies it to a Hermitian
matrix. -/
noncomputable def descEigenvalues {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ℝ :=
  ascEigenvalues M (Fin.cast (Fintype.card_fin n).symm (Fin.rev j))

end GapAgnosticGS.Supplement


