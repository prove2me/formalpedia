-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_centerState
-- name    : MatrixLeeSidford_Supplement_centerState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:18:00.513693+00:00
-- url     : https://prove2.me/theorems/e904260a-b276-4918-a670-cab1f30fcf66
-- title:
--   Query states of one call of Center (Algorithm 4)
-- statement:
--   One call $\mathrm{Center}(P,c,y^\circ)$ with objective $c$ starts at the point $y^\circ$ with weight $G^\circ$ and makes $N_c=(N_G+1)N_y$ oracle queries, numbered $j=0,1,\dots$. Query $j$ is made at the current **query state** $(y_j,G_j)$ and receives an answer $(\hat g_j,\hat R_j,\hat Q_j)$. Queries $j$ with $j\equiv0\pmod{N_G+1}$ are **y-queries**, the others **G-queries**. After query $j$ the call applies:
--
--   1. after a y-query, the damped y-step (8.1)
--   $$
--   y\leftarrow y-\gamma_yP^{-1}(\hat g_j+c),\qquad P:=\alpha\hat Q_0\ \text{(the phase preconditioner, fixed by the first answer)};
--   $$
--   2. after a G-query, the weight update (8.2), $G\leftarrow\mathrm{UpdateWeight}(G,\hat R_j)$.
--
--   If an update reports failure, the call stops. The call returns the point $y_{N_c}$.
--
--   **Formalization Note** The oracle is abstracted to an arbitrary sequence of answers: since the call is deterministic given its answers, an adaptive oracle produces some sequence, so quantifying over all sequences covers every oracle. A failed update gives the value `none` at all later indices. $P^{-1}$ is the matrix inverse (the algorithm solves with the Cholesky factor of $P\succ0$).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Algorithm 4 (procedure Center), p.55; Eqs. (8.1)–(8.2), p.54; Algorithm 8, p.82

import Mathlib
import Definitions.Def_MatrixLeeSidford_Supplement_updateWeight

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **query states of one call of Center** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Algorithm 4, procedure Center, p.55; Eqs. (8.1)
and (8.2), p.54; Algorithm 8, p.82). `centerState … j` is the query state `(y_j, G_j)` — the current point and
weight — at which query `j = 0, 1, …` of the call is made, or `none` if an earlier `UpdateWeight` reported
failure. The call starts at `(y°, G°)`. Query `j` with `j mod (N_G + 1) = 0` is the y-query of loop
`k = j / (N_G + 1)`, the others are its `N_G` G-queries. After query `j` the call applies:
* after a y-query, the damped y-step `y ← y − γ_y P⁻¹(ĝ_j + c)` (Eq. (8.1)) with the phase preconditioner
  `P := α Q̂₀` fixed by the first answer;
* after a G-query, `G ← UpdateWeight(G, R̂_j)` (Eq. (8.2)).

**Formalization Note** The oracle (BarrierOracle, i.e. the data structures) is abstracted: `ans j = (ĝ_j, R̂_j, Q̂_j)`
is the answer to query `j`, an arbitrary sequence. Because the call is deterministic given the answers, an
adaptive (history-dependent) oracle produces some answer sequence, and quantifying over all sequences covers
every oracle. The call makes `N_c = (N_G + 1) N_y` queries; it returns the point of `centerState … N_c`.
`P⁻¹` is Mathlib's matrix inverse (the paper solves with the Cholesky factor of `P ≻ 0`). -/
noncomputable def centerState {m : ℕ} (α γy γG : ℝ) (NG : ℕ) (c y₀ : EuclideanSpace ℝ (Fin m))
    (G₀ : Matrix (Fin m) (Fin m) ℝ)
    (ans : ℕ → EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ) :
    ℕ → Option (EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ)
  | 0 => some (y₀, G₀)
  | j + 1 => (centerState α γy γG NG c y₀ G₀ ans j).bind fun st =>
      if j % (NG + 1) = 0 then
        some (st.1 - γy • WithLp.toLp 2 ((α • (ans 0).2.2)⁻¹ *ᵥ WithLp.ofLp ((ans j).1 + c)), st.2)
      else
        (updateWeight γG st.2 (ans j).2.1).map fun G' => (st.1, G')

end MatrixLeeSidford.Supplement


