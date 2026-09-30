-- Prove2me | Definitions.Def_SabanisEuler_Shared_Model2
-- name    : SabanisEuler_Shared_Model2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T22:55:11.357174+00:00
-- url     : https://prove2.me/theorems/c88768b1-206f-4352-a589-f7d4943cae94
-- title:
--   Model 2: tamed coefficients (2.11)–(2.12) and the 𝔭-condition
-- statement:
--   The tamed Euler coefficients of Sabanis (2016), Model 2, and the numerical part of the $\mathfrak p$-condition.
--
--   1. **Tamed drift and diffusion** (2.11)–(2.12). Given $b,\sigma$ as in the SDE (2.1), exponents $\alpha$ and $l$, and $n\ge1$,
--   $$b_n(t,x):=\frac{1}{1+n^{-\alpha}|x|^l}\,b(t,x),\qquad \sigma_n(t,x):=\frac{1}{1+n^{-\alpha}|x|^l}\,\sigma(t,x),$$
--   for all $t\ge0$ and $x\in\mathbb R^d$.
--   2. **$\mathfrak p$-condition (numerical part).** For $p_0,p_1$ as in A-3–A-6, the exponent $l$ of A-6 and a moment exponent $p$:
--   $$l\le\frac{p_0-2}{4},\qquad 0<p<p_1,\qquad p\le\frac{p_0}{2l+1}.$$
--
--   The paper's $\mathfrak p$-condition also requires the scheme coefficients to be (2.11)–(2.12) with $\alpha=1/2$; in this development that requirement is part of the theorems, whose scheme is driven by the tamed coefficients with $\alpha=1/2$. The division by $1+n^{-\alpha}|x|^l\ge1$ damps the coefficients where $|x|$ is large compared with $n^{\alpha/l}$; this taming is what lets an explicit scheme handle superlinearly growing drift and diffusion.
--
--   **Formalization Note** Powers $n^{-\alpha}$ and $|x|^l$ are real powers; the definitions are only used for $n\ge1$ and $l>0$ (so $|0|^l=0$).
--
--   **Shared definition.** Serves chunks `02-rate` (Model 2, eqs. (2.11)–(2.12), 𝔭-condition, pp. 5–6; previously `SabanisEuler.Rate.Model2`) and `03-uniform-rate` (same pages; previously `SabanisEuler.UniformRate.Model2`). Both copies were identical up to their namespace: `tamedDrift`, `tamedDiffusion` with real powers, and `PCondition` as the numeric part of the 𝔭-condition.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, pp. 5-6, Model 2, eqs. (2.11)–(2.12), 𝔭-condition; shared by chunks 02-rate and 03-uniform-rate

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace SabanisEuler.Shared

open EthierKurtz

variable {d d₁ : ℕ}

/-- Sabanis (2016), p. 5, Model 2, eq. (2.11): the tamed drift
`bₙ(t, x) = b(t, x) / (1 + n^{-α} |x|^l)`, for `n ≥ 1` (`rpow` exponents). -/
noncomputable def tamedDrift (α l : ℝ) (b : ℝ≥0 × SDEState d → SDEState d) (n : ℕ) :
    ℝ≥0 × SDEState d → SDEState d :=
  fun z => (1 + (n : ℝ) ^ (-α) * ‖z.2‖ ^ l)⁻¹ • b z

/-- Sabanis (2016), p. 5, Model 2, eq. (2.12): the tamed diffusion
`σₙ(t, x) = σ(t, x) / (1 + n^{-α} |x|^l)`, for `n ≥ 1` (`rpow` exponents). -/
noncomputable def tamedDiffusion (α l : ℝ) (σ : ℝ≥0 × SDEState d → Diffusion d d₁) (n : ℕ) :
    ℝ≥0 × SDEState d → Diffusion d d₁ :=
  fun z => (1 + (n : ℝ) ^ (-α) * ‖z.2‖ ^ l)⁻¹ • σ z

/-- Sabanis (2016), p. 6, the numeric part of the 𝔭-condition, for the exponent `l` of A-6
and a moment exponent `p`: `l ≤ (p₀ - 2)/4`, `p > 0`, `p < p₁` and `p ≤ p₀ / (2l + 1)`.
The remaining part of the 𝔭-condition (the scheme coefficients are (2.11)–(2.12) with
`α = 1/2`) is built into the theorems, whose scheme uses `tamedDrift (1/2) l b` and
`tamedDiffusion (1/2) l σ`. -/
def PCondition (p₀ p₁ l p : ℝ) : Prop :=
  l ≤ (p₀ - 2) / 4 ∧ 0 < p ∧ p < p₁ ∧ p ≤ p₀ / (2 * l + 1)

end SabanisEuler.Shared


