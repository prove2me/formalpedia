-- Prove2me | Definitions.Def_KeskinZeevi_SufficientConditions_Regret
-- name    : KeskinZeevi_SufficientConditions_Regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T03:45:27.803057+00:00
-- url     : https://prove2.me/theorems/a4a56638-98c8-402f-92d1-e149a65acecf
-- title:
--   T-period regret of a pricing policy
-- statement:
--   The **$T$-period regret** of a policy $\pi$ under the parameter $\theta \in \Theta$ is the expected revenue shortfall relative to a seller who knows $\theta$ and charges $\varphi(\theta)$ in every period:
--   $$\Delta^\pi_\theta(T) = T\, r^*_\theta - \mathbb{E}^\pi_\theta\Big[\sum_{t=1}^T r_\theta(p_t)\Big].$$
--
--   **Formalization Note.** `regret π θ ε P T` takes the expectation as a Bochner integral over the noise space `(Ω, P)`, with $p_t$ given by `price π θ ε t`. The integrand is measurable, because the policy's rules and the noise are measurable, and it is bounded, because prices lie in $[l,u]$. It is therefore integrable, and the Bochner integral has no junk value here.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1145, Eqs. (6)-(7)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_Policy

open MeasureTheory

namespace KeskinZeevi.SufficientConditions

/-- The `T`-period regret `Δ^π_θ(T) = T r*_θ - E[Σ_{t=1}^T r_θ(p_t)]` of policy `π` under
parameter `θ` (Keskin–Zeevi 2014, (6)–(7)), with the expectation taken on the noise space. -/
noncomputable def regret {M : Model} {Ω : Type*} [MeasurableSpace Ω] (π : Policy M)
    (θ : ℝ × ℝ) (ε : ℕ → Ω → ℝ) (P : Measure Ω) (T : ℕ) : ℝ :=
  T * optRevenue θ - ∫ ω, ∑ t ∈ Finset.Icc 1 T, revenue θ (price π θ ε t ω) ∂P

end KeskinZeevi.SufficientConditions


