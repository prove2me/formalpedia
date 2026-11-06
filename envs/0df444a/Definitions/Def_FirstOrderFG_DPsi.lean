-- Prove2me | Definitions.Def_FirstOrderFG_DPsi
-- name    : FirstOrderFG_DPsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:43.008468+00:00
-- url     : https://prove2.me/theorems/38e30da9-97b7-449a-9c5e-0e280bb9dc8f
-- title:
--   Bregman divergence $D_{\Psi_t}$ of the hybrid regularizer (25)
-- statement:
--   The master regularizer at round $t$ is
--   $$
--   \Psi_t(x)=\frac1{\theta_{t,0}}\ln\frac1{x_0}+\frac1\theta\sum_{i\in\bar V_{\mathrm{self}}}\ln\frac1{1-x_i}+\frac1\theta\sum_{i\in\bar V_{\mathrm{self}}}x_i\ln x_i ,
--   $$
--   the first term present only when $0\in\mathcal B$. Being separable, its Bregman divergence is
--   $$
--   D_{\Psi_t}(x,y)=\mathbb I\{0\in\mathcal B\}\frac1{\theta_{t,0}}D_{\varphi_0}(x_0,y_0)+\frac1\theta\sum_{i\in\bar V_{\mathrm{self}}}D_\varphi(x_i,y_i).
--   $$
--
--   **Formalization Note** The rates $\theta_{t,0}$ and $\theta$ are explicit arguments; the divergence is written with the explicit formulas of $D_{\varphi_0}$ and $D_\varphi$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Eq. (25), p.10; Eqs. (81), (84), pp.28–29

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Vbar
import Definitions.Def_FirstOrderFG_Dphi0
import Definitions.Def_FirstOrderFG_Dphi

namespace FirstOrderFG

/-- **The Bregman divergence `D_{Ψ_t}` of the hybrid regularizer (25).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Eq. (25), p.10:
`Ψ_t(x) ≜ (1/θ_{t,0}) ln(1/x₀) + (1/θ) ∑_{i ∈ V̄_self} ln(1/(1 − x_i)) + (1/θ) ∑_{i ∈ V̄_self} x_i ln x_i`,
whose first term is present only when `0 ∈ B`. Since `Ψ_t` is separable,
`D_{Ψ_t}(x, y) = 𝕀{0 ∈ B} (1/θ_{t,0}) D_{φ₀}(x₀, y₀) + (1/θ) ∑_{i ∈ V̄_self} D_φ(x_i, y_i)` (Eq. (81),
p.28, and Eq. (84), p.29).

**Formalization Note.** `DPsi E θ0 θ x y` takes the meta-action rate `θ_{t,0}` and the rate `θ`
of `V̄_self` explicitly; the meta-action `0` is `none`, the action of `i ∈ V̄_self` is `some i`. The
divergence is written through the explicit scalar formulas `Dphi0`, `Dphi`. -/
noncomputable def DPsi {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (θ0 θ : ℝ)
    (x y : Option (Fin K) → ℝ) : ℝ :=
  (if (Vself E).Nonempty then 1 / θ0 * Dphi0 (x none) (y none) else 0)
    + 1 / θ * ∑ i ∈ Vbar E, Dphi (x (some i)) (y (some i))

end FirstOrderFG


