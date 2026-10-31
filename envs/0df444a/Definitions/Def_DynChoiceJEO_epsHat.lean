-- Prove2me | Definitions.Def_DynChoiceJEO_epsHat
-- name    : DynChoiceJEO_epsHat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:53.344017+00:00
-- url     : https://prove2.me/theorems/549a2f0b-ec38-4cc8-ac78-d5f34a8936a1
-- title:
--   Error term $\widehat\epsilon(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]})$
-- statement:
--   For a primal-dual sequence $(x_t,y_t)$, a data sequence $p_t$ and weights $\theta_t$ with $\Theta_T=\sum_t\theta_t$,
--
--   $$\widehat\epsilon\big(\{x_t,y_t;p_t,\theta_t\}_{t\in[T]}\big):=\max_{y\in Y}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x_t,y;p_t)-\min_{x\in X}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\Psi(x,y_t;p_t).$$
--
--   It is the part of the SP-gap bound of Theorem 1 that depends only on the observed data $p_t$, and it splits into the two regrets $\mathcal R_x+\mathcal R_y$ (eq. (12a)).
--
--   **Formalization Note** $[T]$ is `Fin T`; max/min are real suprema/infima of images.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (11a), p.11

import Mathlib

namespace DynChoiceJEO

/-- **Error term `ε̂({x_t,y_t;p_t,θ_t})`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (11a), p.11:
"ϵ̂({x_t,y_t;p_t,θ_t}_{t∈[T]}) := max_{y∈Y} (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x_t,y;p_t)
− min_{x∈X} (1/Θ_T) ∑_{t∈[T]} θ_t Ψ(x,y_t;p_t)".

For sequences `x : Fin T → ℝᴺ`, `y : Fin T → ℝᵏ`, data `pt : Fin T → P` and weights `θ`,
with `Θ_T = ∑ t, θ t`.

**Formalization Note** `[T]` is `Fin T`; max/min are `sSup`/`sInf` of images (finite under
the standing assumptions, since the first objective is concave in y and the second convex in x
when θ ≥ 0). -/
noncomputable def epsHat {N k T : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (X : Set (Fin N → ℝ)) (Y : Set (Fin k → ℝ)) (x : Fin T → Fin N → ℝ)
    (y : Fin T → Fin k → ℝ) (pt : Fin T → P) (θ : Fin T → ℝ) : ℝ :=
  sSup ((fun y' => (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ (x t) y' (pt t)) '' Y)
    - sInf ((fun x' => (∑ t, θ t)⁻¹ * ∑ t, θ t * Ψ x' (y t) (pt t)) '' X)

end DynChoiceJEO


