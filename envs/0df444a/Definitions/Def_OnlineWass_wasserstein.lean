-- Prove2me | Definitions.Def_OnlineWass_wasserstein
-- name    : OnlineWass_wasserstein
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:16.643539+00:00
-- url     : https://prove2.me/theorems/ef889e95-301b-4cfb-8c2d-06b827edcc63
-- title:
--   The Wasserstein distance $\mathcal W$ and the deviation budget $\mathcal W_T$
-- statement:
--   For probability measures $\mathcal Q_1,\mathcal Q_2$ on a metric space, the Wasserstein distance, display (8), is
--
--   $$
--   \mathcal W(\mathcal Q_1,\mathcal Q_2)=\inf_{\mathcal Q_{1,2}\in\mathcal J(\mathcal Q_1,\mathcal Q_2)}\int\rho(\theta_1,\theta_2)\,d\mathcal Q_{1,2}(\theta_1,\theta_2),
--   $$
--
--   where $\mathcal J(\mathcal Q_1,\mathcal Q_2)$ is the set of joint distributions with marginals $\mathcal Q_1$ and $\mathcal Q_2$. The Wasserstein-based deviation budget of a true law $\mathcal P=(\mathcal P_1,\dots,\mathcal P_T)$ from a prior $\hat{\mathcal P}$ is
--
--   $$
--   \mathcal W_T(\mathcal P,\hat{\mathcal P})=\sum_{t=1}^T\mathcal W(\mathcal P_t,\hat{\mathcal P}_t).
--   $$
--
--   This is the quantity that measures how far the prior may be from the truth, and the only place the regret bound sees it.
--
--   **Formalization Note** The set $\mathcal J$ is the published `WassersteinDRO.StrongDuality.couplings`. The value lives in $[0,\infty]$, computed with a lower Lebesgue integral, so it has no junk value, and it is the infimum (8) itself, not a dual form. On the model's $\Theta$, with distance $\rho$ of (2), it is at most 2.
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, (8) and the WBDB, p.20

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_couplings

open MeasureTheory
open scoped ENNReal

namespace OnlineWass

/-- **The Wasserstein distance, (8), p.20.** Jiang, Li & Zhang, arXiv:2012.06961v3:
`𝒲(𝒬₁, 𝒬₂) := inf_{𝒬₁,₂∈𝒥(𝒬₁,𝒬₂)} ∫ ρ(θ₁, θ₂) d𝒬₁,₂(θ₁, θ₂)`, "where 𝒥(𝒬₁, 𝒬₂) denotes all the joint
distributions 𝒬₁,₂ for (θ₁, θ₂) that have marginals 𝒬₁ and 𝒬₂."

**Formalization Note.** `𝒥` is the published `WassersteinDRO.StrongDuality.couplings`. The value is
in `ℝ≥0∞`, with the lower Lebesgue integral of `edist`, so it has no junk value: the set of couplings
contains the product measure, and the distance is the infimum (8), not a Kantorovich–Rubinstein dual. -/
noncomputable def wasserstein {E : Type*} [PseudoEMetricSpace E] [MeasurableSpace E]
    (Q₁ Q₂ : Measure E) : ℝ≥0∞ :=
  ⨅ π ∈ WassersteinDRO.StrongDuality.couplings Q₁ Q₂, ∫⁻ z, edist z.1 z.2 ∂π

/-- **The Wasserstein-based deviation budget (WBDB), p.20:**
`𝒲_T(𝒫, 𝒫̂) := Σ_{t=1}^T 𝒲(𝒫ₜ, 𝒫̂ₜ)`. -/
noncomputable def deviationBudget {E : Type*} [PseudoEMetricSpace E] [MeasurableSpace E] {T : ℕ}
    (P Phat : Fin T → Measure E) : ℝ≥0∞ :=
  ∑ t, wasserstein (P t) (Phat t)

end OnlineWass


