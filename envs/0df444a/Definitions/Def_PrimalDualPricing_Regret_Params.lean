-- Prove2me | Definitions.Def_PrimalDualPricing_Regret_Params
-- name    : PrimalDualPricing_Regret_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:01.389147+00:00
-- url     : https://prove2.me/theorems/7e472ad9-3888-49fe-84b2-7e0a136fb78a
-- title:
--   §3.3, p. 13 — the parameters $\alpha,\tau^{(k)},\bar\Delta^{(k)},\bar\Delta_z^{(k)},N^{(k)},N_z^{(k)},K$ of the primal-dual learning algorithm
-- statement:
--   This file defines the parameters of Algorithm 1 chosen in §3.3, as functions of the algorithm's constant $\epsilon>0$ and the scaling index $n$. Here $\log$ is the natural logarithm and phases are numbered $k=1,\dots,K$:
--   $$\alpha=(\log n)^{1+9\epsilon}n^{-1/4},\qquad \tau^{(k)}=n^{-\frac12(3/5)^{k-1}}(\log n)^{1+15\epsilon},$$
--   $$\bar\Delta^{(k)}=n^{-\frac14(1-(3/5)^{k-1})},\qquad \bar\Delta^{(k)}_z=n^{-\frac14(1-(3/5)^{k-1})}(\log n)^{-2\epsilon},$$
--   $$N^{(k)}=\Big\lceil n^{\frac1{10}(3/5)^{k-1}}(\log n)^{3\epsilon}\Big\rceil,\qquad N^{(k)}_z=\Big\lceil n^{\frac1{10}(3/5)^{k-1}}(\log n)^{\epsilon}\Big\rceil,$$
--   $$K=\min\big\{k\ge1:(\bar\Delta^{(k)})^2\le n^{-1/2}(\log n)^{2+16\epsilon}\big\}.$$
--   Phase $k$ starts at $t_k=\sum_{i=1}^{k-1}\tau^{(i)}$ (so $t_1=0$), and the two test periods of the last phase have length $(\log n)^{-\epsilon}$.
--
--   $\alpha$ is the mark-up of the last phase, $\tau^{(k)}$ the length of phase $k$, $\bar\Delta^{(k)}$ and $\bar\Delta^{(k)}_z$ the widths of the interval estimators before truncation, and $N^{(k)}+1$ and $N^{(k)}_z+1$ the numbers of price and dual grid points.
--
--   **Formalization Note** The page gives $N^{(k)}$ and $N^{(k)}_z$ as real numbers; a grid needs integers, so they are rounded up, which also keeps them $\ge1$. The set defining $K$ is nonempty exactly when $(\log n)^{2+16\epsilon}>1$, i.e. for $n\ge3$, and every result is stated for $n\ge3$; for smaller $n$, Lean's `sInf` of the empty set is $0$, never used. Real powers are `Real.rpow`.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 13, §3.3; p. 9 (t_k); pp. 10–11 (test periods of length (log n)^(−ε))

import Mathlib

namespace PrimalDualPricing.Regret

/-! The parameters of Algorithm 1 chosen in §3.3 (Chen–Gallego, arXiv:1812.09234v3, p. 13), as
functions of the algorithm's constant `ε` (`eps`) and the scaling index `n`. Phases are 1-based as on
the page: `k = 1, …, K`; the value at `k = 0` is unused. `log` is the natural logarithm and real powers
are `Real.rpow`. -/

/-- The mark-up `α = (log n)^{1+9ε} n^{−1/4}`. -/
noncomputable def markup (eps : ℝ) (n : ℕ) : ℝ :=
  Real.log n ^ (1 + 9 * eps) * (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- The phase length `τ^{(k)} = n^{−(1/2)(3/5)^{k−1}} (log n)^{1+15ε}` (used for `k ≤ K − 1`). -/
noncomputable def tau (eps : ℝ) (n k : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ) * (3 / 5 : ℝ) ^ (k - 1)) * Real.log n ^ (1 + 15 * eps)

/-- The pre-truncation width of the price interval estimators,
`Δ̄^{(k)} = n^{−(1/4)(1−(3/5)^{k−1})}`. -/
noncomputable def widthP (n k : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 4 : ℝ) * (1 - (3 / 5 : ℝ) ^ (k - 1)))

/-- The pre-truncation width of the dual interval estimator,
`Δ̄_z^{(k)} = n^{−(1/4)(1−(3/5)^{k−1})} (log n)^{−2ε}`. -/
noncomputable def widthZ (eps : ℝ) (n k : ℕ) : ℝ :=
  widthP n k * Real.log n ^ (-(2 * eps))

/-- The number of price grid intervals `N^{(k)} = ⌈n^{(1/10)(3/5)^{k−1}} (log n)^{3ε}⌉` (the page prints
the real number without rounding; a grid needs an integer, and the ceiling keeps `N^{(k)} ≥ 1`). -/
noncomputable def gridN (eps : ℝ) (n k : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ ((1 / 10 : ℝ) * (3 / 5 : ℝ) ^ (k - 1)) * Real.log n ^ (3 * eps)⌉₊

/-- The number of dual grid points parameter `N_z^{(k)} = ⌈n^{(1/10)(3/5)^{k−1}} (log n)^{ε}⌉`. -/
noncomputable def gridNz (eps : ℝ) (n k : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ ((1 / 10 : ℝ) * (3 / 5 : ℝ) ^ (k - 1)) * Real.log n ^ eps⌉₊

/-- The number of phases `K = min{k ≥ 1 : (Δ̄^{(k)})² ≤ n^{−1/2} (log n)^{2+16ε}}`. The set is nonempty
exactly when `(log n)^{2+16ε} > 1`, i.e. for `n ≥ 3`; every result is stated for `n ≥ 3`. (On an empty
set `sInf` returns `0`, which is never used.) -/
noncomputable def numPhases (eps : ℝ) (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧
    widthP n k ^ 2 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n ^ (2 + 16 * eps)}

/-- The start of phase `k`, `t_k = ∑_{i=1}^{k−1} τ^{(i)}` (so `t_1 = 0`). -/
noncomputable def startTime (eps : ℝ) (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 k, tau eps n i

/-- The length `(log n)^{−ε}` of each of the two test periods of phase `K` (steps 1–2, pp. 10–11). -/
noncomputable def testLen (eps : ℝ) (n : ℕ) : ℝ :=
  Real.log n ^ (-eps)

end PrimalDualPricing.Regret


