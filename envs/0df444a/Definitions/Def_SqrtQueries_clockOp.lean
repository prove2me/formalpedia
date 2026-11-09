-- Prove2me | Definitions.Def_SqrtQueries_clockOp
-- name    : SqrtQueries_clockOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:04.987772+00:00
-- url     : https://prove2.me/theorems/be5e1ef6-d828-4f73-bc28-d5abcf76698f
-- title:
--   Clock operator $D=\sum_j \omega_N^j|j\rangle\langle j|$
-- statement:
--   For an integer $N\ge1$ the **clock operator** on $\mathbb C^N$ is the diagonal unitary
--   $$
--   D=\sum_{j=0}^{N-1}\omega_N^{\,j}\,|j\rangle\langle j|,\qquad \omega_N=e^{2\pi i/N}.
--   $$
--   Its eigenvalues $1,\omega_N,\dots,\omega_N^{N-1}$ are pairwise distinct, so $D$ has a simple spectrum.
--
--   The clock operator is the DIAG oracle $U_0$ of the promise problem of Definition 3.2, and $U_1$ is a conjugate of it.
--
--   **Formalization Note** The paper also writes $D$ for the trace distance (Section 2.4); in this mission the clock is `clockOp` and the trace distance is half of `WildeQIT.traceDist`.
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Section 2.1, p.10

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_omega

namespace SqrtQueries

/-- The **clock operator** `D = ∑_{j=0}^{N−1} ω_N^j |j⟩⟨j|` on `ℂ^N` (Ma–Tang, *Square-root queries
can help*, STOC 2027 submission manuscript, sha256 783868e7…c5f15a, Section 2.1, p.10), with
`ω_N = e^{2πi/N}`.

**Formalization Note.** The basis is `Fin N` and `ω_N^j` is the power by the natural number
`j.val ∈ {0, …, N−1}`; `ω_N = e^{2πi/N}` is the published `MagnonCode.AQEDC.omega N`. The paper's letter `D` also names the trace distance (p.13); in Lean the
clock is `clockOp` and the trace distance is `½ · WildeQIT.traceDist`. -/
noncomputable def clockOp (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun j => MagnonCode.AQEDC.omega N ^ (j : ℕ)

end SqrtQueries


