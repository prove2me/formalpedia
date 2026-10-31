-- Prove2me | Definitions.Def_CardinalMatching_ModParams_xhat
-- name    : CardinalMatching_ModParams_xhat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:05.4154+00:00
-- url     : https://prove2.me/theorems/56febbd6-f213-4e5a-84e5-97e53eac83c8
-- title:
--   The contraction $(\hat x,\hat p)$ to the original instance
-- statement:
--   From the rescaled Step 2 data on $I'$, the contraction to the original instance is
--   $$
--   \hat x_{ij} = \frac1k\sum_{c=1}^{k}\sum_{c'=1}^{k} x_{(i,c),(j,c')},\qquad \hat p_j = \frac1k\sum_{c=1}^{k} p_{(j,c)},
--   $$
--   where $(i,c)$ runs over the $k$ copies of agent $i$ and $(j,c')$ over the $k$ copies of good $j$. The parts of $x$ going to dummy and interpolating agents and to awesome goods are dropped. Theorem 24 shows that $(\hat x,\hat p)$ is a $3/n$-approximate HZ equilibrium.
--
--   **Formalization Note** The paper says "let $\hat x_{ij}$ be the average over all $x_{i'j'}$". The average over the $k^2$ copy pairs would give row sums at most $1/k$, against the proof's "$\sum_j\hat x_{ij}\in[1-1/n,1]$" (for $n=4$, Theorem 24 itself would fail since $1/k<1/4=1-3/n$). The normalization $1/k$ is the one the proof uses. The paper never defines $\hat p$; by Lemma 14 all copies of $j$ have the same price, so $\hat p_j$ is that common price.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Step 5, p.14

import Mathlib
import Definitions.Def_CardinalMatching_ModParams

namespace CardinalMatching

namespace ModParams

variable {n : ℕ} (P : ModParams n)

/-- **The contracted allocation `x̂`** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*,
arXiv:2402.08851v6, Step 5, p.14): for original `i, j`,
`x̂_ij = (1/k) ∑_{c, c'} x_{(i,c),(j,c')}` over the `k` copies `(i, c)` of `i` and the `k` copies
`(j, c')` of `j`; the parts of `x` going to dummy and interpolating agents and to awesome goods
are dropped.

**Formalization Note (correction)** The paper says "let x̂_ij be the average over all x_i′j′"; the
average over the `k²` pairs would make every row sum at most `1/k`, contradicting the proof of
Theorem 24 ("∑_j x̂_ij ∈ [1 − 1/n, 1]") and Theorem 24 itself (e.g. `n = 4`: `1/k < 1/4 = 1 − 3/n`).
The normalization `1/k` (the average over the copies `i'` of the total over the copies `j'`)
is the one under which the proof's sums hold. -/
noncomputable def xhat (x : P.Agent → P.Good → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => (1 / (P.k : ℝ)) * ∑ c : Fin P.k, ∑ c' : Fin P.k, x (Sum.inl (i, c)) (Sum.inl (j, c'))

/-- **The contracted prices `p̂`** (Step 5, p.14): `p̂_j` is the average price of the `k` copies of
good `j`.

**Formalization Note** The paper never defines `p̂`. By Lemma 14 (p.9) all copies of `j` have the
same price, so this is the common copy price, the only reading under which "no agent overspends"
in the proof of Theorem 24 refers to `p̂`. -/
noncomputable def phat (p : P.Good → ℝ) : Fin n → ℝ :=
  fun j => (1 / (P.k : ℝ)) * ∑ c : Fin P.k, p (Sum.inl (j, c))

end ModParams

end CardinalMatching


