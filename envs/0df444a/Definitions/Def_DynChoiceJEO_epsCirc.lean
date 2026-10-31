-- Prove2me | Definitions.Def_DynChoiceJEO_epsCirc
-- name    : DynChoiceJEO_epsCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:06.51106+00:00
-- url     : https://prove2.me/theorems/39fcd5fc-b96f-438b-ba2f-8f63039b29cc
-- title:
--   Data-error term $\epsilon^\circ(\{x_t;p_t,\theta_t\}_{t\in[T]};p)$
-- statement:
--   For a primal sequence $x_t$, data $p_t$, weights $\theta_t$ and the true data $p$,
--
--   $$\epsilon^\circ\big(\{x_t;p_t,\theta_t\}_{t\in[T]};p\big):=\max_{y\in Y}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\big[\Psi(x_t,y;p)-\Psi(x_t,y;p_t)\big].$$
--
--   Together with $\epsilon^\bullet$ it measures the *price of estimation*, the error from using $p_t$ instead of the unknown $p$; it vanishes when $p_t=p$ for all $t$.
--
--   **Formalization Note** The maximum is the real supremum of the image of $Y$. The objective is a difference of concave functions of $y$ and can be unbounded above; theorems that use this term assume the image is bounded above (otherwise the real supremum would be $0$ rather than $+\infty$).
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (11b), p.11

import Mathlib

namespace DynChoiceJEO

/-- **Data-error term `ε°({x_t;p_t,θ_t};p)`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (11b), p.11:
"ϵ◦({x_t;p_t,θ_t}_{t∈[T]};p) := max_{y∈Y} (1/Θ_T) ∑_{t∈[T]} θ_t [Ψ(x_t,y;p) − Ψ(x_t,y;p_t)]".

The supremum over `y ∈ Y` of the weighted average of `Ψ(x_t,y;p) − Ψ(x_t,y;p_t)`: the price of
using the estimate `p_t` instead of the true data `p` on the dual side.

**Formalization Note** max is `sSup` of the image. The objective is a difference of concave
functions of y and need not be bounded above on Y; the theorems using `epsCirc` therefore assume
the image is `BddAbove` (otherwise Lean's `sSup` would be `0` instead of the paper's `+∞`). -/
noncomputable def epsCirc {N k T : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (Y : Set (Fin k → ℝ)) (x : Fin T → Fin N → ℝ) (pt : Fin T → P) (θ : Fin T → ℝ) (p : P) :
    ℝ :=
  sSup ((fun y' => (∑ t, θ t)⁻¹ * ∑ t, θ t * (Ψ (x t) y' p - Ψ (x t) y' (pt t))) '' Y)

end DynChoiceJEO


