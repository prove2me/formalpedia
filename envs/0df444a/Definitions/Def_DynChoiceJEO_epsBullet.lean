-- Prove2me | Definitions.Def_DynChoiceJEO_epsBullet
-- name    : DynChoiceJEO_epsBullet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:08.650993+00:00
-- url     : https://prove2.me/theorems/52eb1019-fa30-4070-a298-608c777db6dd
-- title:
--   Data-error term $\epsilon^\bullet(\{y_t;p_t,\theta_t\}_{t\in[T]};p)$
-- statement:
--   For a dual sequence $y_t$, data $p_t$, weights $\theta_t$ and the true data $p$,
--
--   $$\epsilon^\bullet\big(\{y_t;p_t,\theta_t\}_{t\in[T]};p\big):=\max_{x\in X}\frac1{\Theta_T}\sum_{t\in[T]}\theta_t\big[\Psi(x,y_t;p_t)-\Psi(x,y_t;p)\big].$$
--
--   It is the primal-side price of estimation and vanishes when $p_t=p$ for all $t$.
--
--   **Formalization Note** The maximum is the real supremum of the image of $X$. The objective is a difference of convex functions of $x$ and can be unbounded above; theorems that use this term assume the image is bounded above.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, eq. (11c), p.11

import Mathlib

namespace DynChoiceJEO

/-- **Data-error term `ε•({y_t;p_t,θ_t};p)`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*, arXiv:1702.05702v5, eq. (11c), p.11:
"ϵ•({y_t;p_t,θ_t}_{t∈[T]};p) := max_{x∈X} (1/Θ_T) ∑_{t∈[T]} θ_t [Ψ(x,y_t;p_t) − Ψ(x,y_t;p)]".

The supremum over `x ∈ X` of the weighted average of `Ψ(x,y_t;p_t) − Ψ(x,y_t;p)`: the price of
using the estimate `p_t` instead of the true data `p` on the primal side.

**Formalization Note** max is `sSup` of the image. The objective is a difference of convex
functions of x and need not be bounded above on X; the theorems using `epsBullet` therefore
assume the image is `BddAbove`. -/
noncomputable def epsBullet {N k T : ℕ} {P : Type*} (Ψ : (Fin N → ℝ) → (Fin k → ℝ) → P → ℝ)
    (X : Set (Fin N → ℝ)) (y : Fin T → Fin k → ℝ) (pt : Fin T → P) (θ : Fin T → ℝ) (p : P) :
    ℝ :=
  sSup ((fun x' => (∑ t, θ t)⁻¹ * ∑ t, θ t * (Ψ x' (y t) (pt t) - Ψ x' (y t) p)) '' X)

end DynChoiceJEO


