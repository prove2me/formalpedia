-- Prove2me | Definitions.Def_MatrixSenseRank_Testing_Supplement_Optimization
-- name    : MatrixSenseRank_Testing_Supplement_Optimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:43.96186+00:00
-- url     : https://prove2.me/theorems/3c5bd050-9262-4642-bd5c-5eec490b464d
-- title:
--   Numerical rank-one approximation
-- statement:
--   Let $M\in\mathbb R^{n\times m}$ and $t>0$. A matrix $B\in\mathbb R^{n\times m}$ is a numerical best rank-one approximation of $M$ at tolerance $t$ when $\operatorname{rank}(B)\le1$ and
--
--   $$\|M-B\|_F\le\|M-N\|_F+t\qquad\text{for every }N\text{ with }\operatorname{rank}(N)\le1.$$
--
--   The case $M=0$ is included, and the relation asserts no recovery property of $M$.
--
--   This is the truncation step (Step 3) of Algorithm 1, which takes the best rank-at-most-one approximation of the recovered matrix (cf. Proposition 5); the finite tolerance replaces an exact singular value decomposition in the operational model.
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Proposition 12, Remark 13, Algorithm 1, printed p. 22–26, PDF p. 23–27 (1-based).

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Supplement_Experiments

set_option autoImplicit false
open scoped BigOperators

namespace MatrixSenseRank.Testing.Supplement

/-- Numerical rank-one truncation at absolute Frobenius tolerance tol, including M=0.
`B` has rank at most one and is within `tol` of the best rank-at-most-one approximation
of `M` in Frobenius norm (Algorithm 1, Step 3; Proposition 5). -/
def ApproxRankOne {n m : ℕ} (M B : Mat n m) (tol : ℝ) : Prop :=
  B.rank ≤ 1 ∧ ∀ N : Mat n m, N.rank ≤ 1 → frobenius (M - B) ≤ frobenius (M - N) + tol

end MatrixSenseRank.Testing.Supplement


