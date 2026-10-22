-- Prove2me | Definitions.Def_KeskinZeevi_LowerBound_Regret
-- name    : KeskinZeevi_LowerBound_Regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:28:30.661114+00:00
-- url     : https://prove2.me/theorems/6aad9c85-3d3c-4757-a0b0-330a9aaafad3
-- title:
--   Expected revenue, regret, worst-case regret and squared pricing error
-- statement:
--   Fix a probability space $(\Omega, P)$, demand shocks $\varepsilon_t$ on it, a policy $\pi$ and a parameter $\theta$. Let $p_t(\omega)$ be the price the policy charges in period $t$ when the shocks are $\varepsilon_1(\omega), \varepsilon_2(\omega), \dots$. The following quantities are defined.
--
--   - The expected $T$-period revenue (6): $R^\pi_\theta(T) = \mathbb{E}\big[\sum_{t=1}^T r_\theta(p_t)\big]$.
--   - The $T$-period **regret** (7): $\Delta^\pi_\theta(T) = T\, r^*_\theta - R^\pi_\theta(T)$.
--   - The **worst-case regret** (8):
--   $$\Delta^\pi(T) = \sup\{\Delta^\pi_\theta(T) : \theta \in \Theta\}.$$
--   - The expected squared pricing error in period $t$: $\mathbb{E}(p_t - \varphi(\theta))^2$.
--
--   **Formalization Note.** Expectations are Bochner integrals with respect to $P$. Every integrand is bounded, because prices lie in $[l,u]$. It is also measurable whenever the shocks are, because the policy's rules are measurable. So each expectation is a genuine one. The supremum is taken over the subtype $\Theta$, which is nonempty. The family is bounded above: $\Delta^\pi_\theta(T) = -\beta\sum_t \mathbb{E}(p_t-\varphi(\theta))^2 \le |b_{\min}|(u-l)^2 T$. So the real `iSup` is the true supremum. Lean period $t$ is the paper's period $t+1$, so the sums $\sum_{t=1}^T$ run over Lean periods $0,\dots,T-1$, and `sqErr … t` is $\mathbb{E}(p_{t+1}-\varphi(\theta))^2$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, pp. 1144-1145, Eqs. (6), (7), (8)

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy

namespace KeskinZeevi.LowerBound

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The price charged in Lean period `t` (the paper's `p_{t+1}`) at the sample point `ω`, when
the seller uses `π`, the parameter is `θ`, and the demand shocks are `ε`. -/
noncomputable def price {l u : ℝ} (π : Policy l u) (θ : ℝ × ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  pricePath π θ (fun s => ε s ω) t

/-- Expected `T`-period revenue (6): `R^π_θ(T) = E^π_θ[Σ_{t=1}^T r_θ(p_t)]`, the sum running
over Lean periods `0, …, T − 1`. -/
noncomputable def expRevenue (P : Measure Ω) (ε : ℕ → Ω → ℝ) {l u : ℝ} (π : Policy l u)
    (θ : ℝ × ℝ) (T : ℕ) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.range T, revenue θ (price π θ ε t ω) ∂P

/-- The `T`-period regret (7): `Δ^π_θ(T) = T r*_θ − R^π_θ(T)`. -/
noncomputable def regret (P : Measure Ω) (ε : ℕ → Ω → ℝ) {l u : ℝ} (π : Policy l u)
    (θ : ℝ × ℝ) (T : ℕ) : ℝ :=
  (T : ℝ) * optRevenue θ - expRevenue P ε π θ T

/-- The worst-case regret (8): `Δ^π(T) = sup {Δ^π_θ(T) : θ ∈ Θ}`, a supremum over the subtype
`Θ` (nonempty, and the family is bounded above because prices lie in `[l, u]`). -/
noncomputable def worstRegret (M : Model) (P : Measure Ω) (ε : ℕ → Ω → ℝ)
    (π : Policy M.l M.u) (T : ℕ) : ℝ :=
  ⨆ θ : M.Θ, regret P ε π (θ : ℝ × ℝ) T

/-- The expected squared pricing error in Lean period `t`: `E^π_θ (p_{t+1} − φ(θ))²`. -/
noncomputable def sqErr (P : Measure Ω) (ε : ℕ → Ω → ℝ) {l u : ℝ} (π : Policy l u)
    (θ : ℝ × ℝ) (t : ℕ) : ℝ :=
  ∫ ω, (price π θ ε t ω - optPrice θ) ^ 2 ∂P

end KeskinZeevi.LowerBound


