-- Prove2me | Definitions.Def_SubspaceConv_zeta
-- name    : SubspaceConv_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:10.691296+00:00
-- url     : https://prove2.me/theorems/73e58efe-b6fe-47c9-bb8e-bf1a71af4697
-- title:
--   The truncated subspace zeta transform $Z_{n,k}$
-- statement:
--   For a table $f$ on the subspaces of $\mathbb F_q^n$ of dimension at most $k$, with values in a commutative coefficient ring $R$,
--   $$(Z_{n,k}f)(W)=\sum_{\substack{U\le W\\ \dim U\le k}}f(U),\qquad W\le\mathbb F_q^n,\ \dim W\le k.$$
--   Its matrix is the $M_q(n,k)\times M_q(n,k)$ matrix with entries $\mathbf 1[U\le W]$; ordered by dimension it is triangular with diagonal one, hence invertible over every ring. For $k=n$ it is the full zeta transform $Z_n$ of eq. (1).
--
--   **Formalization Note** Values may lie in any additive commutative monoid; the sum ranges over the finite type of subspaces of dimension at most $k$.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), eq. (1), p.1; §1.1, pp.1–2

import Mathlib
import Definitions.Def_SubspaceConv_SubLE

namespace SubspaceConv

open Classical in
/-- The truncated subspace zeta transform `Z_{n,k}`: `(Z_{n,k} f)(W) = ∑_{U ≤ W, dim U ≤ k} f(U)`
for `W` of dimension at most `k` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), eq. (1), p.1, and §1.1, pp.1–2:
"the `M_q(n,k) × M_q(n,k)` matrix with entries `1[U ≤ W]`").

**Formalization Note** A table is a function on `SubLE F n k` with values in any additive
commutative monoid `A` (the paper's commutative coefficient ring). -/
noncomputable def zeta {F : Type*} [Field F] [Finite F] {n k : ℕ} {A : Type*} [AddCommMonoid A]
    (f : SubLE F n k → A) (W : SubLE F n k) : A :=
  ∑ U : SubLE F n k, if U.1 ≤ W.1 then f U else 0

end SubspaceConv


