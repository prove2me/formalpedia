-- Prove2me | Definitions.Def_HScattered_Hyperplanes_sigma
-- name    : HScattered_Hyperplanes_sigma
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:57.717724+00:00
-- url     : https://prove2.me/theorems/510155af-06df-43d5-bd77-9f43faa48341
-- title:
--   Elementary symmetric polynomial $\sigma_{k,l}$ at $1,q,\dots,q^k$ (Definition 5.4)
-- statement:
--   For real $q$ and $k, l \in \mathbb N$, $\sigma_{k,l}$ is the $l$-th elementary symmetric polynomial in the $k+1$ variables $x_0,\dots,x_k$ evaluated at $x_i = q^i$:
--   $$\sigma_{k,l} = \sum_{0 \le i_1 < \cdots < i_l \le k} q^{\,i_1 + \cdots + i_l}.$$
--   Thus $\sigma_{k,0} = 1$ and $\sigma_{k,l} = 0$ for $l > k+1$.
--
--   These numbers appear as the coefficients when the product $(x-1)(x-q)\cdots(x-q^{k})$ is expanded in powers of $x$, which is how §5.3 uses them.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 19, Definition 5.4 (explicit sum on p. 21)

import Mathlib

namespace HScattered.Hyperplanes

/-- Definition 5.4 (arXiv:1906.10590v2, p. 19, and p. 21): `σ_{k,l}` is the `l`-th elementary
symmetric polynomial in the `k + 1` variables `1, q, q², …, q^k`, i.e.
`σ_{k,l} = ∑_{0 ≤ i₁ < ⋯ < i_l ≤ k} q^{i₁ + ⋯ + i_l}`. It is `1` for `l = 0` and `0` for
`l > k + 1`. -/
def sigma (q : ℝ) (k l : ℕ) : ℝ :=
  ∑ T ∈ (Finset.range (k + 1)).powersetCard l, q ^ (∑ i ∈ T, i)

end HScattered.Hyperplanes


