-- Prove2me | Definitions.Def_BernoulliPoA_binomExp
-- name    : BernoulliPoA_binomExp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:11.195411+00:00
-- url     : https://prove2.me/theorems/4655df43-4ff5-4a71-a306-924a16f2876d
-- title:
--   Binomial expectation $c^q$
-- statement:
--   The **binomial expectation** of a cost function $c$ is
--   $$
--   c^q(k)=q\,\mathsf E[c(1+X)],\qquad X\sim\mathrm{Binomial}(k-1,q),
--   $$
--   that is,
--   $$
--   c^q(k)=q\sum_{j=0}^{k-1}\binom{k-1}{j}q^j(1-q)^{k-1-j}\,c(1+j).
--   $$
--   It is the expected cost, per unit of load, of a resource used by $k$ players each of whom participates with probability $q$.
--
--   **Formalization Note** At $k=0$, where the display has no meaning, the sum is empty and $c^q(0)=0$. The paper reads this value only multiplied by $m=0$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (18), p.14

import Mathlib

namespace BernoulliPoA

/-- **Binomial expectation** `c^q`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §2.2, display (18), p.14: `c^q(k) = q E[c(1 + X)]` with
`X ∼ Binomial(k - 1, q)`, written out as `q ∑_{j=0}^{k-1} C(k-1, j) q^j (1-q)^{k-1-j} c(1 + j)`.

**Formalization Note** The subtractions are in `ℕ` and correct for `j < k`. At `k = 0`, where (18) has no meaning, the range is
empty and `c^q(0) = 0`; the paper only reads this value multiplied by `m = 0` (in (28), (EC.1)). `c 0` is never read. -/
noncomputable def binomExp (c : ℕ → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  q * ∑ j ∈ Finset.range k, ((k - 1).choose j : ℝ) * q ^ j * (1 - q) ^ (k - 1 - j) * c (1 + j)

end BernoulliPoA


