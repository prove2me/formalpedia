-- Prove2me | Definitions.Def_OnlineWass_IsFluidPlan
-- name    : OnlineWass_IsFluidPlan
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:49.774992+00:00
-- url     : https://prove2.me/theorems/d7520891-44db-4e17-aec6-93fe3a75e868
-- title:
--   The prior plan $(\hat p^*,\hat x)$ of (9)–(10), corrected, and $\hat\gamma_t$
-- statement:
--   Fix a budget $c$ and a prior $\hat{\mathcal P}_1,\dots,\hat{\mathcal P}_T$. For a measurable $\hat x:\Theta\to\mathcal X$ let
--
--   $$
--   \hat\gamma_t=\hat{\mathcal P}_t\,g(\hat x(\theta);\theta)=\int g(\hat x(\theta);\theta)\,d\hat{\mathcal P}_t(\theta).
--   $$
--
--   A pair $(\hat p^*,\hat x)$ is a **fluid plan** if
--
--   1. $\hat p^*\ge0$ and $\hat x$ is measurable with values in $\mathcal X$;
--   2. $\hat x(\theta)$ maximizes $f(x;\theta)-(\hat p^*)^\top g(x;\theta)$ over $x\in\mathcal X$, for every $\theta$;
--   3. $\sum_{t=1}^T\hat\gamma_t\le c$ coordinatewise;
--   4. $(\hat p^*)^\top\bigl(c-\sum_{t=1}^T\hat\gamma_t\bigr)=0$.
--
--   The sequence $\hat\gamma$ is the input of the algorithm IGD($\hat\gamma$): the budget it plans to spend in each period.
--
--   **Formalization Note** Display (10) writes $\hat x(\theta)=\operatorname{argmax}$, which is a set under ties, and a free choice from it invalidates the paper's Lemma 5 and the regret bound. So 3 and 4 are required. Every minimizer of $\hat L$ extends to a plan (`OnlineWass.exists_fluid_plan`), and when the argmax is unique the printed $\hat x$ is that one. That $\hat p^*$ minimizes $\hat L$ is not listed, because it follows (`OnlineWass.lemma_5`). A single map $\hat x$, rather than one per period, is the printed shape.
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, (9), (10), p.21, corrected

import Mathlib
import Definitions.Def_OnlineWass_Model

open MeasureTheory

namespace OnlineWass

variable {k m : ℕ} {Θ : Type*} [MeasurableSpace Θ]

/-- **`γ̂ₜ`, (10), p.21:** `γ̂ₜ := 𝒫̂ₜ g(x̂(θ); θ) = ∫ g(x̂(θ); θ) d𝒫̂ₜ(θ)`. -/
noncomputable def gammaHat {T : ℕ} (M : Model k m Θ) (Phat : Fin T → Measure Θ)
    (xhat : Θ → Fin k → ℝ) (t : Fin T) (i : Fin m) : ℝ :=
  ∫ θ, M.g (xhat θ) θ i ∂Phat t

/-- **The prior plan of (9)–(10), p.21, corrected.** `(p̂*, x̂)` with `p̂* ≥ 0`, `x̂ : Θ → 𝒳` measurable,
`x̂(θ)` a maximizer of `f(x; θ) − (p̂*)ᵀg(x; θ)` over `𝒳` for every `θ`, `Σₜγ̂ₜ ≤ c`, and complementary
slackness `(p̂*)ᵀ(c − Σₜγ̂ₜ) = 0`.

**Formalization Note.** The paper's (10) writes `x̂(θ) = argmax`, which is a set under ties, and for a
free choice from that set Lemma 5 (31) and the regret bound fail. So the tie-break is required to be
complementary; `OnlineWass.exists_fluid_plan` shows every minimizer of `L̂` has one, and when the argmax
is unique the printed `x̂` is that one. `p̂* ∈ argmin L̂` is not a field: it follows
(`OnlineWass.lemma_5`). One map `x̂ : Θ → 𝒳`, not one per `t`, is the printed shape. -/
structure IsFluidPlan {T : ℕ} (M : Model k m Θ) (c : Fin m → ℝ) (Phat : Fin T → Measure Θ)
    (phat : Fin m → ℝ) (xhat : Θ → Fin k → ℝ) : Prop where
  phat_nonneg : 0 ≤ phat
  measurable_xhat : Measurable xhat
  xhat_mem : ∀ θ, xhat θ ∈ M.X
  isMaxOn : ∀ θ, IsMaxOn (fun x => M.lagrangian phat x θ) M.X (xhat θ)
  budget_le : ∀ i, ∑ t, gammaHat M Phat xhat t i ≤ c i
  slackness : ∑ i, phat i * (c i - ∑ t, gammaHat M Phat xhat t i) = 0

end OnlineWass


