-- Prove2me | Definitions.Def_CubeSampling_Npar
-- name    : CubeSampling_Npar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:21:45.06352+00:00
-- url     : https://prove2.me/theorems/5520314e-1025-4cd5-8c25-a910acaa75cf
-- title:
--   Definition 1.3 — parametric threshold $N_{\mathrm{par}}(d,k,m,A,\delta)$
-- statement:
--   **Definition 1.3.** Let $\sigma^2 > 0$ be the noise variance and $A \ge 16$. $N_{\mathrm{par}}(d,k,m,A,\delta)$ is the least integer $N \ge 1$ such that
--   $$
--   R_{n,\delta}(d,k,m) \le A\sigma^2\,\frac{m + \log(1/\delta)}{n} \qquad \text{for every } n \ge N .
--   $$
--
--   **Formalization Note** The value lies in $\mathbb N \cup \{\infty\}$ and is $\infty$ when no such $N$ exists; the noise level $\sigma$ is an explicit argument.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Definition 1.3, p.4

import Mathlib
import Definitions.Def_CubeSampling_worstRisk
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Definition 1.3, the parametric threshold `N_par(d, k, m, A, δ)`: the least integer `N ≥ 1` such
that `R_{n,δ}(d, k, m) ≤ Aσ² (m + log(1/δ)) / n` for every `n ≥ N` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Definition 1.3, p.4).

**Formalization Note** The value lies in `ℕ∞` and is `⊤` when no such `N` exists; the noise level
`σ` is an explicit argument. -/
noncomputable def Npar (d k m : ℕ) (A σ δ : ℝ) : ℕ∞ :=
  sInf ((fun N : ℕ => (N : ℕ∞)) '' {N : ℕ | 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    worstRisk d k m σ n δ ≤ ENNReal.ofReal (A * σ ^ 2 * (m + Real.log (1 / δ)) / n)})

end CubeSampling


