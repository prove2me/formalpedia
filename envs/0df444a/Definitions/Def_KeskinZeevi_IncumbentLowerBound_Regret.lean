-- Prove2me | Definitions.Def_KeskinZeevi_IncumbentLowerBound_Regret
-- name    : KeskinZeevi_IncumbentLowerBound_Regret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:50:48.935341+00:00
-- url     : https://prove2.me/theorems/d147a1e8-8163-4738-bbd8-743fb114938b
-- title:
--   Price deviation, regret, worst-case regret (22), squared pricing error and the information metric (24)
-- statement:
--   Fix a model, a probability space $(\Omega, P)$ carrying demand shocks $\epsilon$, a policy $\pi$ and a slope $\beta$. Let $p_t$ be the price process of the policy, and let $x_t = p_t - \hat p$ be the **price deviation** in period $t$. The following quantities are defined for a horizon $T$.
--
--   - The expected $T$-period revenue is $R^\pi_\beta(T) = \mathbb E^\pi_\beta \sum_{t=1}^T r_\beta(x_t)$, which is (6) with $\theta, p_t$ replaced by $\beta, x_t$.
--   - The $T$-period **regret** is (7) with $\theta, p_t, \varphi$ replaced by $\beta, x_t, \psi$:
--   $$\Delta^\pi_\beta(T) = T\, r_\beta(\psi(\beta)) - R^\pi_\beta(T).$$
--   - The **worst-case regret** (22) is
--   $$\Delta^\pi(T) = \sup\{\Delta^\pi_\beta(T) : b_{\min} \le \beta \le b_{\max},\ \psi(\beta) \ne 0\}.$$
--   - The expected squared pricing error in period $t$ is $\mathbb E^\pi_\beta (x_t - \psi(\beta))^2$.
--   - The expected **information metric** (24) is $\mathbb E^\pi_\beta[\hat J_t]$, where $\hat J_t = \sum_{s=1}^t x_s^2$ and $\hat J_0 = 0$.
--
--   **Formalization Note.** Lean period $t$ is the paper's period $t+1$. So `dev … t` is $x_{t+1}$, `sqErr … t` is $\mathbb E^\pi_\beta(x_{t+1} - \psi(\beta))^2$, and `expInfo … t` is $\mathbb E^\pi_\beta[\hat J_t]$, which sums over Lean periods $0, \dots, t-1$. Expectations are Bochner integrals of bounded functions, because prices lie in $[l,u]$. They are measurable whenever the shocks are measurable. The worst-case regret is a real supremum over the subtype $\{\beta \in \mathfrak B : \psi(\beta) \ne 0\}$. That subtype is nonempty: $\psi$ vanishes at most once on $\mathfrak B$ because $\hat D \ne 0$, and $b_{\min} < b_{\max}$. The family is bounded above uniformly in $\beta$, so the supremum is the paper's.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1149, Section 3.4, Eqs. (22) and (24), with (6)-(7) of p. 1145

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Model
import Definitions.Def_KeskinZeevi_IncumbentLowerBound_Policy

namespace KeskinZeevi.IncumbentLowerBound

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The price deviation `x_{t+1} = p_{t+1} − p̂` of Lean period `t` (the paper's period `t + 1`)
on the sample point `ω`, when the seller uses `π`, the slope is `β`, and the demand shocks
are `ε` (p. 1149). -/
noncomputable def dev (M : Model) (π : Policy M.l M.u) (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  pricePath M π β (fun s => ε s ω) t - M.pHat

/-- Expected `T`-period revenue, (6) with `θ, p_t` replaced by `β, x_t` (p. 1149):
`R^π_β(T) = E^π_β[Σ_{t=1}^T r_β(x_t)]`. The integrand is bounded (prices lie in `[l, u]`) and
measurable (the policy's rules and the shocks are measurable), so this is a genuine
expectation. -/
noncomputable def expRevenue (M : Model) (P : Measure Ω) (ε : ℕ → Ω → ℝ) (π : Policy M.l M.u)
    (β : ℝ) (T : ℕ) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.range T, M.revenue β (dev M π β ε t ω) ∂P

/-- The `T`-period regret, (7) with `θ, p_t, φ` replaced by `β, x_t, ψ` (p. 1149):
`Δ^π_β(T) = T r_β(ψ(β)) − R^π_β(T)`. -/
noncomputable def regret (M : Model) (P : Measure Ω) (ε : ℕ → Ω → ℝ) (π : Policy M.l M.u)
    (β : ℝ) (T : ℕ) : ℝ :=
  (T : ℝ) * M.revenue β (M.optDev β) - expRevenue M P ε π β T

/-- The worst-case regret (22): `Δ^π(T) = sup {Δ^π_β(T) : bMin ≤ β ≤ bMax, ψ(β) ≠ 0}`, a
supremum over the subtype `M.Bexcl`, which is nonempty (`bMin < bMax` and `ψ` is injective on
`𝔅` because `D̂ ≠ 0`); the family is bounded above because prices lie in `[l, u]`. -/
noncomputable def worstRegret (M : Model) (P : Measure Ω) (ε : ℕ → Ω → ℝ)
    (π : Policy M.l M.u) (T : ℕ) : ℝ :=
  ⨆ β : M.Bexcl, regret M P ε π (β : ℝ) T

/-- The expected squared pricing error in Lean period `t`: `E^π_β (x_{t+1} − ψ(β))²`. -/
noncomputable def sqErr (M : Model) (P : Measure Ω) (ε : ℕ → Ω → ℝ) (π : Policy M.l M.u)
    (β : ℝ) (t : ℕ) : ℝ :=
  ∫ ω, (dev M π β ε t ω - M.optDev β) ^ 2 ∂P

/-- The expected information metric (24): `E^π_β[Ĵ_t]` with `Ĵ_t = Σ_{s=1}^t x_s²`, the sum of
the squared price deviations of the first `t` periods (Lean periods `0, …, t − 1`);
`Ĵ_0 = 0`. -/
noncomputable def expInfo (M : Model) (P : Measure Ω) (ε : ℕ → Ω → ℝ) (π : Policy M.l M.u)
    (β : ℝ) (t : ℕ) : ℝ :=
  ∫ ω, ∑ s ∈ Finset.range t, (dev M π β ε s ω) ^ 2 ∂P

end KeskinZeevi.IncumbentLowerBound


