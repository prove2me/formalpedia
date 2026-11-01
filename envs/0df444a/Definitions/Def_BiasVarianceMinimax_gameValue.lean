-- Prove2me | Definitions.Def_BiasVarianceMinimax_gameValue
-- name    : BiasVarianceMinimax_gameValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:41.812611+00:00
-- url     : https://prove2.me/theorems/0af66639-64e3-45a0-84c8-4f92e6415783
-- title:
--   The class $\mathcal F_K$ and the worst-case risk
-- statement:
--   For $K>0$, the calibration class is $\mathcal F_K=\{g(\cdot):g(d)\le Kd\}$, where $g$ maps $\mathbb R_+$ to $\mathbb R_+$: it says how the estimator may set $\tilde d$ as a function of the baseline's $d$. For $g$ and an array $W$, the worst-case risk is
--
--   $$\max_{\hat\theta(\cdot)\in\Theta,\ d>0}R^{gen}(\hat\theta(\cdot),d,g(d),W).$$
--
--   The asymptotic minimax risk ratio is the minimum of this quantity over $g\in\mathcal F_K$ and $W$. The array and $g$ come first and do not see the model; $g$ sees $d$.
--
--   **Formalization Note** `calibrationClass K` asks $0<g(d)\le Kd$ for all $d>0$. `gameValue` is the supremum in $[0,\infty]$: for a general $W$ the $\max$ need not be attained.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, §5.1, p.20

import Mathlib
import Definitions.Def_BiasVarianceMinimax_riskRatio

open scoped ENNReal

namespace BiasVarianceMinimax

/-- The calibration class `𝓕_K = {g(·) : g(d) ≤ K d}`. Lam, Zhang & Zhang, arXiv:1902.04673v1,
§5.1, p.20.

**Formalization Note.** `g` maps `ℝ₊` to `ℝ₊` (p.13; §5 keeps this, since `δⱼ > 0`), so membership
asks `0 < g d ≤ K d` for all `d > 0`. The values of `g` at `d ≤ 0` are never read. -/
def calibrationClass (K : ℝ) : Set (ℝ → ℝ) :=
  {g | ∀ d : ℝ, 0 < d → 0 < g d ∧ g d ≤ K * d}

/-- The worst-case risk `max_{θ̂(·)∈Θ, d>0} R^gen(θ̂(·), d, g(d), W)` of a calibration `g` and an
array `W`. Lam, Zhang & Zhang, arXiv:1902.04673v1, §5.1, p.20.

**Formalization Note.** The inner `max` is read as a supremum in `ℝ≥0∞`: for a general `W` it need
not be attained. `W` and `g` are fixed before the model, and `g` sees `d` and nothing else. -/
noncomputable def gameValue (q₁ q₂ : ℝ) (n₀ : ℕ) (g : ℝ → ℝ) (W : TriangularArray) : ℝ≥0∞ :=
  ⨆ (M : SimulationOutput q₁ q₂) (d : {d : ℝ // 0 < d}), riskRatio M n₀ d (g d) W

end BiasVarianceMinimax


