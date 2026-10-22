-- Prove2me | Definitions.Def_KeskinZeevi_IncumbentSufficient_Regret
-- name    : KeskinZeevi_IncumbentSufficient_Regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:35:37.407576+00:00
-- url     : https://prove2.me/theorems/d0578deb-ce7b-4b95-bf23-bbd42d2c9997
-- title:
--   T-period regret in the incumbent price problem
-- statement:
--   The $T$-period **regret** of a policy $\pi$ under slope $\beta$ is the expected revenue shortfall relative to always charging the optimal price $\hat p + \psi(\beta)$:
--   $$\Delta^\pi_\beta(T) = T\, r_\beta(\psi(\beta)) - \mathbb{E}^\pi_\beta\Big[\sum_{t=1}^T r_\beta(x_t)\Big].$$
--
--   **Formalization Note.** This is (6)–(7) of the paper with $\theta, p_t, \varphi$ replaced by $\beta, x_t, \psi$, as §3.4 prescribes. The expectation is the integral over the noise space of the sum along the price process of `Policy`. The integrand is bounded and measurable, so the integral is a genuine expectation.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1145, Eqs. (6)-(7), as modified on p. 1148 (after Eq. (21))

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentSufficient_Policy

open MeasureTheory

namespace KeskinZeevi.IncumbentSufficient

/-- The `T`-period regret `Δ^π_β(T) = T r_β(ψ(β)) - E[Σ_{t=1}^T r_β(x_t)]` of policy `π` under
slope `β` in the incumbent price problem (Keskin–Zeevi 2014, (6)–(7) with `θ, p_t, φ` replaced by
`β, x_t, ψ`, p. 1148), with the expectation taken on the noise space. -/
noncomputable def regret {M : Model} {Ω : Type*} [MeasurableSpace Ω] (π : Policy M)
    (β : ℝ) (ε : ℕ → Ω → ℝ) (P : Measure Ω) (T : ℕ) : ℝ :=
  T * M.optRevenue β - ∫ ω, ∑ t ∈ Finset.Icc 1 T, M.revenue β (dev π β ε t ω) ∂P

end KeskinZeevi.IncumbentSufficient


