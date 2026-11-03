-- Prove2me | Definitions.Def_MobilePromo_Assumption1
-- name    : MobilePromo_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:41.093949+00:00
-- url     : https://prove2.me/theorems/f39c2edf-9335-436f-a9e4-47ce1f681ff7
-- title:
--   Assumption 1: smooth, log-concave, increasing win curves
-- statement:
--   For every location $l$, the win curve is twice continuously differentiable in $(\gamma_l,b_l)$ on $\Gamma_l\times B$, and for every $\gamma_l\in\Gamma_l^{(0)}$ and $b_l\in B$,
--
--   $$
--   b\mapsto\log p_l(\gamma_l,b)\ \text{ is concave on }B,\qquad p_l(\gamma_l,b_l)\in(0,1),\qquad \frac{\partial p_l(\gamma_l,b_l)}{\partial b_l}>0 .
--   $$
--
--   Linear, exponential and logit win curves satisfy this for suitable sets. It bounds the win probability away from $0$ and $1$ on $B$, and makes the per-period optimal bid unique.
--
--   **Formalization Note** Because $B$ is closed, the smoothness is `ContDiffOn` on the product $\Gamma_l\times B$, and $\partial p_l/\partial b_l$ is the derivative within $B$, one-sided at the two end points.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Assumption 1, p.12

import Mathlib
import Definitions.Def_MobilePromo_Model

set_option autoImplicit false

namespace MobilePromo

/-- Assumption 1 on the win curves (SSRN 3523491, Assumption 1, p.12): `p_l` is twice continuously
differentiable in `(γ_l, b_l)` on `Γ_l × B`, and for `γ_l ∈ Γ_l⁽⁰⁾` it is log concave in `b_l` on `B`, has
values in `(0, 1)` on `B`, and has `∂p_l/∂b_l > 0` on `B`.

**Formalization Note** `B` is closed, so the smoothness is `ContDiffOn` on the product `Γ_l × B`, and
`∂p_l/∂b_l` is the derivative within `B` (one-sided at the two end points). -/
structure Assumption1 (M : Model) : Prop where
  contDiffOn : ∀ l, ContDiffOn ℝ 2 (fun x : Param (M.n l) × ℝ => M.p l x.1 x.2) (M.Γ l ×ˢ M.B)
  logConcave : ∀ l, ∀ γ ∈ M.Γ₀ l, ConcaveOn ℝ M.B (fun b => Real.log (M.p l γ b))
  pos : ∀ l, ∀ γ ∈ M.Γ₀ l, ∀ b ∈ M.B, 0 < M.p l γ b
  lt_one : ∀ l, ∀ γ ∈ M.Γ₀ l, ∀ b ∈ M.B, M.p l γ b < 1
  deriv_pos : ∀ l, ∀ γ ∈ M.Γ₀ l, ∀ b ∈ M.B, 0 < derivWithin (M.p l γ) M.B b

end MobilePromo


