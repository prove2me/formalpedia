-- Prove2me | Definitions.Def_KServerConj_confDist
-- name    : KServerConj_confDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:41.199739+00:00
-- url     : https://prove2.me/theorems/5bf1693c-6806-41cb-b5f9-d7304375abc2
-- title:
--   Distance $D(X,Y)$ between configurations (minimum-cost matching), equation (1)
-- statement:
--   Let $(M,d)$ be a (pseudo)metric space. A **configuration** is a finite set of points of $M$ (in the $k$-server problem, the $k$ server locations). For configurations $X=\{x_1,\dots,x_k\}$ and $Y=\{y_1,\dots,y_k\}$ of the same size, their **distance** is the minimum cost of a perfect matching between them,
--
--   $$D(X,Y)=\min_{\sigma\in S_k}\sum_{i=1}^k d(x_i,y_{\sigma(i)}).$$
--
--   It is the minimum total distance the servers travel when moving from $X$ to $Y$.
--
--   **Formalization Note** Configurations are `Finset M`. The minimum over permutations is the infimum over bijections $e:X\to Y$ of $\sum_{x\in X} d(x,e(x))$; for $|X|=|Y|$ this is a minimum over a finite nonempty set. For sets of different sizes there is no bijection and the value is the junk value $0$; the mission only uses $D$ between sets of equal size $k$.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, equation (1), p.1 (pdf p.2)

import Mathlib

namespace KServerConj

/-- **The distance between two configurations**, equation (1) of Coester, Koutsoupias, Zbysiński,
*The k-server conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…),
§1.1, printed p.1 (PDF p.2):

"For configurations X = {x₁, …, x_k} and Y = {y₁, …, y_k}, their distance is
D(X, Y) = min_{σ∈S_k} ∑_{i=1}^k d(x_i, y_{σ(i)})."

It is the minimum cost of moving the servers from `X` to `Y`.

**Formalization Note.** Configurations are finite sets `X Y : Finset M`. The minimum over
permutations is the infimum over bijections `e : X ≃ Y` of `∑_{x ∈ X} d(x, e x)`; for
`X.card = Y.card` the index type is finite and nonempty, so the infimum is attained. For sets of
different cardinality there is no bijection and the value is the junk `0`; every statement of the
mission uses `confDist` only between sets of the same cardinality `k`. -/
noncomputable def confDist {M : Type*} [PseudoMetricSpace M] (X Y : Finset M) : ℝ :=
  ⨅ e : X ≃ Y, ∑ x : X, dist (x : M) (e x : M)

end KServerConj


