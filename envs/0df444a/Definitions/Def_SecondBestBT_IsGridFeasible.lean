-- Prove2me | Definitions.Def_SecondBestBT_IsGridFeasible
-- name    : SecondBestBT_IsGridFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:28.110032+00:00
-- url     : https://prove2.me/theorems/4298c2e2-90bf-43fb-a300-11627719a541
-- title:
--   Feasible grid allocation (constraints of Corollary 3.2)
-- statement:
--   A grid allocation matrix $x\in[0,1]^{(N+1)^2}$ is **feasible** for grid priors $f_S,f_B$ on $D$ if
--
--   1. $x(i,j)\in[0,1]$ for all $i,j\le N$;
--   2. the buyer interims $(x_B(j))_{j=0}^N$ are weakly increasing;
--   3. the seller interims $(x_S(i))_{i=0}^N$ are weakly decreasing;
--   4. $\Lambda^D_D(x)\ge0$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Corollary 3.2, p.6; Lemma 3.3, p.7

import Mathlib
import Definitions.Def_SecondBestBT_lambdaDD

namespace SecondBestBT

/-- The constraints of the finite-grid program of Corollary 3.2 (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Corollary 3.2, p.6): a matrix in
`[0, 1]^{(N+1)²}` whose buyer interims `(x_B(j))_j` are weakly increasing, whose seller interims
`(x_S(i))_i` are weakly decreasing, and with `Λ^D_D(x) ≥ 0`. The paper calls such a matrix a
feasible grid allocation (Lemma 3.3, p.7).

**Formalization Note** Monotonicity is over all indices in `{0, …, N}` (`Set.Iic N`). -/
def IsGridFeasible (t : ℕ → ℝ) (fS fB : ℕ → ℝ) (N : ℕ) (x : ℕ → ℕ → ℝ) : Prop :=
  (∀ i ≤ N, ∀ j ≤ N, x i j ∈ Set.Icc (0 : ℝ) 1) ∧
  MonotoneOn (gridInterimB fS N x) (Set.Iic N) ∧
  AntitoneOn (gridInterimS fB N x) (Set.Iic N) ∧
  0 ≤ lambdaDD t fS fB N x

end SecondBestBT


