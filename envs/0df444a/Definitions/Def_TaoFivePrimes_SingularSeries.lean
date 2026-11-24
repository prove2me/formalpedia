-- Prove2me | Definitions.Def_TaoFivePrimes_SingularSeries
-- name    : TaoFivePrimes_SingularSeries
-- status  : Definition
-- author  : @andreaskapfer
-- created : 2026-09-17T06:54:29.20055+00:00
-- url     : https://prove2.me/theorems/061c3a0a-11a8-465a-b6ed-f595bb990c09
-- title:
--   Tao's twin prime constant and pair-sieve weight $f(n)=1_{(n,2)=1}\mu^2(n)\prod_{p|n,p>2}1/(p-2)$
-- statement:
--   ## The twin prime constant and the pair-sieve weight
--
--   The **twin prime constant** is the Euler product
--   $$\mathfrak{S}_2 \;=\; 2 \prod_{p>2}\Bigl(1-\frac{1}{(p-1)^2}\Bigr),$$
--   the leading factor $2$ being the contribution of the prime $2$ to the singular series of the prime-pair problem. The formalization works with the **partial products**
--   $$\mathfrak{S}_2(Q) \;=\; \prod_{\substack{p \le Q \\ p > 2}}\Bigl(1-\frac{1}{(p-1)^2}\Bigr), \qquad Q \in \mathbb{N},$$
--   and defines the constant as $2\inf_Q \mathfrak{S}_2(Q)$, twice the infimum of the range of the partial products. Every factor lies in $(0,1)$, so the partial products decrease; the infimum therefore coincides with the infinite product, while the formulation by an infimum keeps the estimate `every finite partial product dominates the full product' elementary, with no convergence machinery.
--
--   The second object is the **pair-sieve weight** used in Tao's proof of Proposition 4.10,
--   $$f(n) \;=\; \mathbf{1}_{(n,2)=1}\,\mu^2(n)\prod_{\substack{p \mid n \\ p>2}}\frac{1}{p-2},$$
--   which records that $n$ is odd (the indicator $(n,2)=1$) and squarefree (the factor $\mu^2(n)$), and attaches the local factor $1/(p-2)$ at each odd prime divisor of $n$.
--
--   In Lean these are `TaoFivePrimes.twinPrimePartial`, `TaoFivePrimes.twinPrimeConstant` and `TaoFivePrimes.pairSieveWeight`.
-- source:
--   Terence Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656v4, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10 (Section 4): the twin prime constant $\mathfrak{S}_2 = 2\prod_{p>2}(1-1/(p-1)^2)$ and the sieve weight $f(n)=\mathbf{1}_{(n,2)=1}\mu^2(n)\prod_{p\mid n, p>2}1/(p-2)$.

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The twin prime constant and Tao's pair-sieve weight

Source: Terence Tao, *Every odd number greater than 1 is the sum of at most
five primes*, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

The twin prime constant is the Euler product
`𝔖₂ = 2 ∏_{p>2} (1 - 1/(p-1)²)`, and the multiplicative weight `f` used in
the prime-pair sieve expansion is
`f(n) = 𝟙_{(n,2)=1} μ²(n) ∏_{p|n, p>2} 1/(p-2)`.

The infinite product is defined as twice the infimum of its partial products
`∏_{2<p≤Q} (1 - 1/(p-1)²)` over `Q`. Since each factor lies in `(0,1)`, the
partial products form a decreasing sequence whose limit is this infimum, so
the value coincides with the infinite product; the infimum formulation keeps
the facts needed in sieve estimates (every finite partial product dominates
the full product) elementary, with no convergence machinery.
-/

open scoped BigOperators

namespace TaoFivePrimes

/-- The partial Euler product over the odd primes `p` with `2 < p ≤ Q`. -/
noncomputable def twinPrimePartial (Q : ℕ) : ℝ :=
  ∏ p ∈ Finset.range (Q + 1),
    if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- The twin prime constant `𝔖₂ = 2 ∏_{p>2} (1 - 1/(p-1)²)`, defined as twice
the infimum over `Q` of the partial products `twinPrimePartial Q`. -/
noncomputable def twinPrimeConstant : ℝ :=
  2 * sInf (Set.range twinPrimePartial)

/-- Tao's pair-sieve weight
`f(n) = 𝟙_{(n,2)=1} μ²(n) ∏_{p|n, p>2} 1/(p-2)`
from the proof of Proposition 4.10. The condition `n % 2 = 1` encodes
`(n,2)=1`, and `Squarefree n` encodes `μ²(n) = 1`. -/
noncomputable def pairSieveWeight (n : ℕ) : ℝ :=
  if n % 2 = 1 ∧ Squarefree n then
    ∏ p ∈ Nat.primeFactors n, if 2 < p then 1 / ((p : ℝ) - 2) else 1
  else 0

end TaoFivePrimes


