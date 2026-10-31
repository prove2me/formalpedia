-- Prove2me | Definitions.Def_DynChoiceJEO_Ry
-- name    : DynChoiceJEO_Ry
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:12.092384+00:00
-- url     : https://prove2.me/theorems/f5a42782-ef6f-4ba5-bf3c-d01a1176fe20
-- title:
--   Dual regret $\mathcal R_y(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]})$
-- statement:
--   The weighted regret of the dual sequence $y_t$ against the best fixed $y\in Y$ for the gains $\Psi(x_t,\cdot;p_t)$:
--
--   $$\mathcal R_y\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big):=\max_{y\in Y}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x_t,y;p_t)-\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x_t,y_t;p_t).$$
--
--   Online convex optimization algorithms make this term $O(1/\sqrt T)$.
--
--   **Formalization Note** The maximum is the real supremum of the image of $Y$.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (12c), p.13

import Mathlib

namespace DynChoiceJEO

/-- **Dual regret `R_y({x_t,y_t;p_t,θ_t})`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (12c), p.13:
"R_y({x_t,y_t;p_t,θ_t}_{t∈[T]}) := max_{y∈Y} (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x_t,y;p_t)
− (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x_t,y_t;p_t)".

The weighted regret of the dual sequence `y_t` against the best fixed `y ∈ Y` for the gains
`Ψ(x_t,·;p_t)`.

**Formalization Note** max is `sSup` of the image; `Θ_T = ∑ t, θ t`. -/
noncomputable def Ry {N k T : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (Y : Set (Fin k → ℝ)) (x : Fin T → Fin N → ℝ) (y : Fin T → Fin k → ℝ) (pt : Fin T → P)
    (θ : Fin T → ℝ) : ℝ :=
  sSup ((fun y' => (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ (x t) y' (pt t)) '' Y)
    - (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ (x t) (y t) (pt t)

end DynChoiceJEO


