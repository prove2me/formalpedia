-- Prove2me | Definitions.Def_KServerConj_colDet
-- name    : KServerConj_colDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:22.591878+00:00
-- url     : https://prove2.me/theorems/c0c3f39a-556a-4359-9a20-a13d9e62a905
-- title:
--   Determinant $u(X)=\det(q_{x_1},\dots,q_{x_k})$ of $k$ columns
-- statement:
--   Given a column $q_x\in K^k$ for every point $x\in M$ and a tuple $X=(x_1,\dots,x_k)$ of points, let
--
--   $$u(X)=\det(q_{x_1},\dots,q_{x_k}),$$
--
--   the determinant of the $k\times k$ matrix whose $j$-th column is $q_{x_j}$. The algebraic state of the proof represents the work function through these determinants: $\nu(u(X))=w(\{x_1,\dots,x_k\})$ (equation (10)).
--
--   **Formalization Note** Coordinates are indexed by $\{0,\dots,k-1\}$. For a tuple with a repeated point the determinant is $0$.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §2.3, equation (10), p.7 (pdf p.8)

import Mathlib
import Definitions.Def_KServerConj_K

namespace KServerConj

/-- **The determinant of `k` columns**, `u(X) = det(q_{x₁}, …, q_{x_k})`, Coester, Koutsoupias,
Zbysiński, *The k-server conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256
7ca0380a…), equation (10), §2.3, printed p.7 (PDF p.8).

Given a column `q x ∈ K^k` for every point `x`, and a tuple `X = (x₁, …, x_k)`, `colDet q X` is the
determinant of the `k × k` matrix whose `j`-th column is `q (X j)`.

**Formalization Note.** Coordinates are indexed by `Fin k`, the paper's `1, …, k` shifted by one.
For a tuple with a repeated point the determinant is `0`, whose valuation is `⊤`. -/
noncomputable def colDet {k : ℕ} {M : Type*} (q : M → Fin k → K k M) (X : Fin k → M) : K k M :=
  (Matrix.of fun i j => q (X j) i).det

end KServerConj


