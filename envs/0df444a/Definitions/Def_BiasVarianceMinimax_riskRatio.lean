-- Prove2me | Definitions.Def_BiasVarianceMinimax_riskRatio
-- name    : BiasVarianceMinimax_riskRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:46.175252+00:00
-- url     : https://prove2.me/theorems/8bfa9985-3b09-4e56-adbd-72cc961c5c39
-- title:
--   The asymptotic risk ratio $R^{gen}$
-- statement:
--   A triangular array is a family $W=(w_{j,n})_{j=1,\dots,n;\ n=1,2,\dots}$ of real numbers, one weight vector per budget. The asymptotic risk ratio of the weighted estimator against the baseline is
--
--   $$R^{gen}(\hat\theta(\cdot),d,\tilde d,W)=\limsup_{n\to\infty}\frac{\mathrm{MSE}_1^{gen}(\hat\theta(\cdot),\tilde d,w^{(n)})}{\mathrm{MSE}_0(\hat\theta(\cdot),d)} .$$
--
--   **Formalization Note** The value lies in $[0,\infty]$, because the ratio can be unbounded: for instance an array whose sums do not tend to $1$ has value $\infty$ against some model. $\mathrm{MSE}_0$ is positive for all large $n$, so the convention $x/0=0$ at finitely many $n$ is not read by the $\limsup$.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, §5.1, p.19

import Mathlib
import Definitions.Def_BiasVarianceMinimax_mseBaseline
import Definitions.Def_BiasVarianceMinimax_mseWeighted

open Filter
open scoped ENNReal

namespace BiasVarianceMinimax

/-- A triangular array of real weights `W = (w_{j,n})_{j=1,…,n; n=1,2,…}`, of any sign.
Lam, Zhang & Zhang, arXiv:1902.04673v1, §5.1, pp.19–20. Entry `W n i` is `w_{i+1,n}`. -/
abbrev TriangularArray : Type := ∀ n : ℕ, Fin n → ℝ

/-- The asymptotic risk ratio `R^gen(θ̂(·), d, d̃, W) = limsup MSE₁^gen / MSE₀`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, §5.1, p.19.

**Formalization Note.** The value lies in `ℝ≥0∞`, because the ratio can be unbounded and a real
`limsup` would then be junk. `MSE₀` is positive for all large `n` (proved in the verification file),
so the division by zero at finitely many `n` is not read by the `limsup`. -/
noncomputable def riskRatio {q₁ q₂ : ℝ} (M : SimulationOutput q₁ q₂) (n₀ : ℕ) (d dTilde : ℝ)
    (W : TriangularArray) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal (mseWeighted M n₀ dTilde n (W n) / mseBaseline M n₀ d n)) atTop

end BiasVarianceMinimax


