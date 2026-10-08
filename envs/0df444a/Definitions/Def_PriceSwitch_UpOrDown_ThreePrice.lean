-- Prove2me | Definitions.Def_PriceSwitch_UpOrDown_ThreePrice
-- name    : PriceSwitch_UpOrDown_ThreePrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:30.561315+00:00
-- url     : https://prove2.me/theorems/7986dcc0-eb66-4ba3-ae6f-41910f05bd52
-- title:
--   §5, pp. 1384–1385 — three prices p₁ < p < p₂, J(n,t;0) = max{J¹,J²}, Δ¹, Δ², Δ, the thresholds t¹_n, t²_n, t_n, and J(n,t)
-- statement:
--   This module sets up the markup-or-markdown problem of §5 of Feng and Gallego (1995).
--
--   Sales start at price $p$ with Poisson intensity $\lambda$, and once during the horizon the price may be changed either down to $p_1$ or up to $p_2$, with intensities $\lambda_1$ and $\lambda_2$. The standing assumptions are
--
--   $$
--   p_1 < p < p_2, \qquad \lambda_1 > \lambda > \lambda_2, \qquad r_1 > r > r_2,
--   $$
--
--   where $r_i = p_i\lambda_i$, $r = p\lambda$, and all prices and intensities are positive. Note that in this section $p_1$ is the *lower* price.
--
--   For $i = 1, 2$ let $J^i(n,t;s)$ be the expected revenue of selling at $p$ over the first $s$ time units and at $p_i$ afterwards (the two-price $J(n,t;s)$ of the model with $(a,b) = (p,p_i)$), and define:
--
--   1. $J(n,t;0) = \max\{J^1(n,t;0), J^2(n,t;0)\}$, the revenue of switching immediately to the better alternative;
--   2. $\Delta^i(n,t) = J(n,t;t) - J^i(n,t;0)$ for $i = 1,2$, where $J(n,t;t) = p\,E\min(n,N(t))$ is the revenue of keeping $p$;
--   3. $\Delta(n,t) = \Delta^2(n,t) - \Delta^1(n,t) = J^1(n,t;0) - J^2(n,t;0)$;
--   4. the thresholds
--   $$
--   t^i_n = \inf\{t > 0 : \Delta^i(n,t) = 0\}, \qquad t_n = \inf\{t > 0 : \Delta(n,t) = 0\};
--   $$
--   5. the optimal revenue
--   $$
--   J(n,t) = \sup_{\tau \in \mathcal T} E\bigl[p\,\min(n, N(\tau)) + J(n - N(\tau), t - \tau; 0)\bigr],
--   $$
--   where $N$ is the demand process at $p$ and $\mathcal T$ the stopping times of its history with $0 \le \tau \le t$ and $N(\tau) \le n$ almost surely. This is the paper's $\sup_{\tau} E I(n,t;\tau)$.
--
--   These are the objects of Theorem 3.
--
--   **Formalization Note** Every function takes the six parameters $(p_1, \lambda_1, p, \lambda, p_2, \lambda_2)$ in this order, even where a parameter is not read (e.g. $\Delta^1$ does not read $p_2, \lambda_2$); this keeps the signatures uniform. The infima are Lean's `sInf` over sets of reals, which returns $0$ on the empty set; by Lemma 3 each set is nonempty under the standing assumptions. The demand at $p$ is the referenced counting process, with $N(\cdot)$ taking the place of $N_1(\cdot)$ (p. 1385).
-- source:
--   Feng & Gallego (1995), Management Science 41(8), §5, pp. 1384–1385, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- §5 (p. 1384): the three prices of the markup-or-markdown problem, `p₁ < p < p₂` with Poisson rates
`λ₁ > λ > λ₂` and revenue rates `r₁ > r > r₂` (`r_i = p_i λ_i`, `r = p λ`). The initial price is `p`;
`p₁` is the lower and `p₂` the higher alternative. Prices and rates are positive. -/
structure IsThreePrice (p₁ lam₁ p lam p₂ lam₂ : ℝ) : Prop where
  pos_price : 0 < p₁
  pos_rate : 0 < lam₂
  price_lt₁ : p₁ < p
  price_lt₂ : p < p₂
  rate_lt₁ : lam < lam₁
  rate_lt₂ : lam₂ < lam
  rev_lt₁ : p * lam < p₁ * lam₁
  rev_lt₂ : p₂ * lam₂ < p * lam

/-- `J(n, t; 0) = max{J¹(n, t; 0), J²(n, t; 0)}` (p. 1385), where
`J^i(n, t; s) = PriceSwitch.Markdown.switchRevenue p lam p_i lam_i n t s` starts at `p` and switches to `p_i` at `s`. -/
noncomputable def switchNowMax (p₁ lam₁ p lam p₂ lam₂ : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  max (PriceSwitch.Markdown.switchRevenue p lam p₁ lam₁ m u 0) (PriceSwitch.Markdown.switchRevenue p lam p₂ lam₂ m u 0)

/-- `Δ¹(n, t) = J(n, t; t) − J¹(n, t; 0)` (p. 1385). -/
noncomputable def delta1 (p₁ lam₁ p lam p₂ lam₂ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  PriceSwitch.Markdown.switchRevenue p lam p₁ lam₁ n t t - PriceSwitch.Markdown.switchRevenue p lam p₁ lam₁ n t 0

/-- `Δ²(n, t) = J(n, t; t) − J²(n, t; 0)` (p. 1385). -/
noncomputable def delta2 (p₁ lam₁ p lam p₂ lam₂ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  PriceSwitch.Markdown.switchRevenue p lam p₂ lam₂ n t t - PriceSwitch.Markdown.switchRevenue p lam p₂ lam₂ n t 0

/-- `Δ(n, t) = Δ²(n, t) − Δ¹(n, t) = J¹(n, t; 0) − J²(n, t; 0)` (p. 1385). -/
noncomputable def delta (p₁ lam₁ p lam p₂ lam₂ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  PriceSwitch.Markdown.switchRevenue p lam p₁ lam₁ n t 0 - PriceSwitch.Markdown.switchRevenue p lam p₂ lam₂ n t 0

/-- `t¹_n = inf{t > 0 : Δ¹(n, t) = 0}` (p. 1385). -/
noncomputable def tThr1 (p₁ lam₁ p lam p₂ lam₂ : ℝ) (n : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ delta1 p₁ lam₁ p lam p₂ lam₂ n t = 0}

/-- `t²_n = inf{t > 0 : Δ²(n, t) = 0}` (p. 1385). -/
noncomputable def tThr2 (p₁ lam₁ p lam p₂ lam₂ : ℝ) (n : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ delta2 p₁ lam₁ p lam p₂ lam₂ n t = 0}

/-- `t_n = inf{t > 0 : Δ(n, t) = 0}` (p. 1385). -/
noncomputable def tThr (p₁ lam₁ p lam p₂ lam₂ : ℝ) (n : ℕ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ delta p₁ lam₁ p lam p₂ lam₂ n t = 0}

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `J(n, t) = sup_{τ ∈ 𝒯} E I(n, t; τ)` (p. 1385), with
`I(n, t; s) = p E min(n, N(s)) + E J(n − N(s), t − s; 0)` and `N = countingProcess T` the demand at the
initial price `p` (the caller assumes `IsExpInterarrivals P lam T`). -/
noncomputable def optRevenue3 (P : Measure Ω) (T : ℕ → Ω → ℝ) (p₁ lam₁ p lam p₂ lam₂ : ℝ) (n : ℕ)
    (t : ℝ) : ℝ :=
  PriceSwitch.Markdown.stopValue P T p (switchNowMax p₁ lam₁ p lam p₂ lam₂) n t

end PriceSwitch.UpOrDown


