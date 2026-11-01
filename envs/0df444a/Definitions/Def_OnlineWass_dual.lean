-- Prove2me | Definitions.Def_OnlineWass_dual
-- name    : OnlineWass_dual
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:53.930087+00:00
-- url     : https://prove2.me/theorems/f3d2252d-594a-4887-a03e-e0f2ba1c70db
-- title:
--   The dual functions $h$, $L_{\mathcal Q}$, $L$ and $\hat L$
-- statement:
--   For $p\in\mathbb R^m$ and $\theta\in\Theta$, the dual integrand is
--
--   $$
--   h(p;\theta)=\max_{x\in\mathcal X}\bigl\{f(x;\theta)-p^\top g(x;\theta)\bigr\}.
--   $$
--
--   For a probability measure $\mathcal Q$ on $\Theta$, $L_{\mathcal Q}(p)=\int h(p;\theta')\,d\mathcal Q(\theta')$, and for a sequence $\mathcal P=(\mathcal P_1,\dots,\mathcal P_T)$ the dual function is
--
--   $$
--   L(p)=p^\top c+\sum_{t=1}^T L_{\mathcal P_t}(p).
--   $$
--
--   Evaluated on a prior $\hat{\mathcal P}$ this is $\hat L$, and `IsDualMinimizer` is display (9), $\hat p^*\in\operatorname{argmin}_{p\ge0}\hat L(p)$.
--
--   These functions carry the primal-dual analysis of the regret.
--
--   **Formalization Note** The maximum is a real supremum over a nonempty bounded set, attained because $\mathcal X$ is compact. Under the model's hypotheses $h(p;\cdot)$ is bounded and Lipschitz, so the integral is an honest Bochner integral for every probability measure.
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, pp.14, 21, display (9)

import Mathlib
import Definitions.Def_OnlineWass_Model

open MeasureTheory

namespace OnlineWass

variable {k m : ℕ} {Θ : Type*}

/-- **The dual integrand, p.14:** `h(p; θ) := max_{x∈𝒳} { f(x; θ) − pᵀg(x; θ) }`.

**Formalization Note.** A real `sSup` over a nonempty set, bounded under `Assumption1ab` and attained
because `𝒳` is compact. -/
noncomputable def h (M : Model k m Θ) (p : Fin m → ℝ) (θ : Θ) : ℝ :=
  sSup ((fun x => M.lagrangian p x θ) '' M.X)

/-- **`L_𝒬`, p.21:** `L_𝒬(p) := 𝒬h(p; θ) = ∫_{θ'∈Θ} h(p; θ') d𝒬(θ')`.

**Formalization Note.** A Bochner integral. Under `DistEqRho` and `Assumption1ab`, `h(p; ·)` is
Lipschitz and bounded, hence integrable for every finite measure `𝒬`; no integrability is assumed. -/
noncomputable def LQ [MeasurableSpace Θ] (M : Model k m Θ) (Q : Measure Θ) (p : Fin m → ℝ) : ℝ :=
  ∫ θ, h M p θ ∂Q

/-- **The dual function, pp.14, 21:** `L(p) = pᵀc + Σ_{t=1}^T L_{𝒫ₜ}(p)`. Applied to the prior
`𝒫̂` it is `L̂(p) = pᵀc + Σ_{t=1}^T L_{𝒫̂ₜ}(p)`. -/
noncomputable def dual [MeasurableSpace Θ] {T : ℕ} (M : Model k m Θ) (c : Fin m → ℝ)
    (P : Fin T → Measure Θ) (p : Fin m → ℝ) : ℝ :=
  ∑ i, p i * c i + ∑ t, LQ M (P t) p

/-- **(9), p.21:** `p̂* ∈ argmin_{p≥0} L̂(p)`, read at `P = 𝒫̂`. -/
def IsDualMinimizer [MeasurableSpace Θ] {T : ℕ} (M : Model k m Θ) (c : Fin m → ℝ)
    (P : Fin T → Measure Θ) (p : Fin m → ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : Fin m → ℝ, 0 ≤ p' → dual M c P p ≤ dual M c P p'

end OnlineWass


