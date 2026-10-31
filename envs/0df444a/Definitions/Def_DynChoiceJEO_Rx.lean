-- Prove2me | Definitions.Def_DynChoiceJEO_Rx
-- name    : DynChoiceJEO_Rx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:10.66902+00:00
-- url     : https://prove2.me/theorems/bd3199f9-5d9f-4a81-98d1-90535542b41b
-- title:
--   Primal regret $\mathcal R_x(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]})$
-- statement:
--   The weighted regret of the primal sequence $x_t$ against the best fixed $x\in X$ for the losses $\Psi(\cdot,y_t;p_t)$:
--
--   $$\mathcal R_x\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big):=\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x_t,y_t;p_t)-\min_{x\in X}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x,y_t;p_t).$$
--
--   **Formalization Note** The minimum is the real infimum of the image of $X$.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (12b), p.13

import Mathlib

namespace DynChoiceJEO

/-- **Primal regret `R_x({x_t,y_t;p_t,θ_t})`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (12b), p.13:
"R_x({x_t,y_t;p_t,θ_t}_{t∈[T]}) := (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x_t,y_t;p_t)
− min_{x∈X} (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x,y_t;p_t)".

The weighted regret of the primal sequence `x_t` against the best fixed `x ∈ X` for the losses
`Ψ(·,y_t;p_t)`.

**Formalization Note** min is `sInf` of the image; `Θ_T = ∑ t, θ t`. -/
noncomputable def Rx {N k T : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (X : Set (Fin N → ℝ)) (x : Fin T → Fin N → ℝ) (y : Fin T → Fin k → ℝ) (pt : Fin T → P)
    (θ : Fin T → ℝ) : ℝ :=
  (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ (x t) (y t) (pt t)
    - sInf ((fun x' => (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ x' (y t) (pt t)) '' X)

end DynChoiceJEO


