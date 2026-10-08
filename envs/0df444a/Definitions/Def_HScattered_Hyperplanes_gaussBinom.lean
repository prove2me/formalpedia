-- Prove2me | Definitions.Def_HScattered_Hyperplanes_gaussBinom
-- name    : HScattered_Hyperplanes_gaussBinom
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:58.764365+00:00
-- url     : https://prove2.me/theorems/9466f812-6d20-4b7d-b617-49d503016c85
-- title:
--   Gaussian binomial coefficient $[n\ k]_q$ by formula (15)
-- statement:
--   For a real number $q$ and natural numbers $n,k$, the **Gaussian binomial coefficient** is
--   $$\begin{bmatrix} n\\ k\end{bmatrix}_q = \begin{cases} 1 & k = 0,\\[2pt] \dfrac{(1-q^n)(1-q^{n-1})\cdots(1-q^{n-k+1})}{(1-q^k)(1-q^{k-1})\cdots(1-q)} & 1 \le k \le n,\\[6pt] 0 & k > n.\end{cases}$$
--
--   For a prime power $q$ it counts the $k$-dimensional subspaces of $\mathbb F_q^n$; the paper uses it as a rational function of $q$ in the identities of §5, where coefficients "out of range" ($k > n$) are zero.
--
--   **Formalization Note** The coefficient is defined by the product formula (15) for every real $q$ (not as a subspace count). For $q > 1$ no denominator vanishes; all theorems using it assume $q > 1$. The case $k = 0$ is the empty quotient $1/1$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 18, §5.1, formula (15)

import Mathlib

namespace HScattered.Hyperplanes

/-- The Gaussian binomial coefficient `[n k]_q`, by formula (15) of arXiv:1906.10590v2, p. 18:
it is `1` if `k = 0`,
`(1 − qⁿ)(1 − q^{n−1})⋯(1 − q^{n−k+1}) / ((1 − q^k)(1 − q^{k−1})⋯(1 − q))` if `1 ≤ k ≤ n`,
and `0` if `k > n`. It is defined for a real parameter `q`; for `q > 1` every denominator
is nonzero. At `k = 0` both products are empty, so the middle branch gives `1`. -/
noncomputable def gaussBinom (q : ℝ) (n k : ℕ) : ℝ :=
  if n < k then 0
  else (∏ i ∈ Finset.range k, (1 - q ^ (n - i))) / (∏ i ∈ Finset.range k, (1 - q ^ (k - i)))

end HScattered.Hyperplanes


