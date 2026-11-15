-- Prove2me | Definitions.Def_LG2021_RegretRate
-- name    : LG2021_RegretRate
-- status  : Definition
-- author  : @sim2000dg
-- created : 2026-11-14T15:28:33.293731+00:00
-- url     : https://prove2.me/theorems/b312da5e-97cc-46be-9c7a-3bc1dcd45ba7
-- title:
--   Explicit stochastic convex-bandit regret rate
-- statement:
--   For dimension $d\ge1$, horizon $n\ge2$, and diameter $D\ge2$, define
--   $$R(d,D,n)=d^{9/2}\sqrt n\,[\log(nD)]^{3/2}\max\!\left\{1,\frac{\sqrt{\log(nD)}}{d}\right\}.$$
--   This is the explicit rate in Theorems 1 and 2 of Lattimore and György (COLT 2021). The Lean expression uses $d^4\sqrt d$ and $\log(nD)\sqrt{\log(nD)}$ for the fractional powers. This entry defines the rate; the regret guarantee is proved in the corresponding theorem entries.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Theorems 1 and 2, printed p. 1.

import Mathlib

noncomputable section

namespace LG2021

/-- The explicit dimension, horizon, and diameter dependence in the regret bound. -/
def sharpRate (d : ℕ) (D : ℝ) (n : ℕ) : ℝ :=
  (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n *
    (Real.log ((n : ℝ) * D) * Real.sqrt (Real.log ((n : ℝ) * D))) *
      max 1 (Real.sqrt (Real.log ((n : ℝ) * D)) / (d : ℝ))

end LG2021


