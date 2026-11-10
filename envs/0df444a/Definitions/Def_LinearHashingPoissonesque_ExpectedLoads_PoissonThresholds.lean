-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds
-- name    : LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:10.399174+00:00
-- url     : https://prove2.me/theorems/8276b26f-c3f9-4d9e-bc95-d105899a1062
-- title:
--   Upper and lower Poisson Chernoff thresholds
-- statement:
--   Let $m>0$ be real and let $n,r$ be integers with $1\le r\le n$. Put $\mu=m/n$ and $c=\log(n/r)$. The upper threshold is the unique real root at or above the mean, while the lower threshold has a zero branch:
--
--   $$T_r^+(m,n)\ge\mu,\quad D(T_r^+(m,n),\mu)=c,$$
--   $$T_r^-(m,n)=0\ \text{if }\mu\le c;\qquad 0<T_r^-(m,n)\le\mu,\quad D(T_r^-(m,n),\mu)=c\ \text{if }c<\mu.$$
--
--   These are real analytic Chernoff thresholds, without integer rounding. At $r=n$, both equal $\mu$. At $\mu=c$, the lower threshold is exactly zero. They are not Poisson quantiles or expected order statistics.
--
--   **Formalization Note** Each nonzero-branch threshold is the real infimum of its root set. The separate, sorry-free local verification module proves existence, uniqueness and the characterizing equations for every real $m>0$ on the stated domain. Thus each such root set is a singleton, and the real infimum has no empty-set or unbounded-set default. No expected-load bound occurs in these definitions.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.14, Definition 1, Eq.(3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonDivergence

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Definition 1, p.14: unique upper root, encoded as the infimum of the root set.
Existence and uniqueness on the source domain are proved separately. -/
noncomputable def upperThreshold (m : ℝ) (n r : ℕ) : ℝ :=
  sInf {t : ℝ | m / (n : ℝ) ≤ t ∧
    poissonDivergence t (m / (n : ℝ)) = Real.log ((n : ℝ) / (r : ℝ))}

/-- Definition 1, p.14: exactly the zero branch at μ ≤ log(n/r); otherwise the lower root. -/
noncomputable def lowerThreshold (m : ℝ) (n r : ℕ) : ℝ :=
  if m / (n : ℝ) ≤ Real.log ((n : ℝ) / (r : ℝ)) then 0 else
    sInf {t : ℝ | 0 < t ∧ t ≤ m / (n : ℝ) ∧
      poissonDivergence t (m / (n : ℝ)) = Real.log ((n : ℝ) / (r : ℝ))}

end LinearHashingPoissonesque.ExpectedLoads


