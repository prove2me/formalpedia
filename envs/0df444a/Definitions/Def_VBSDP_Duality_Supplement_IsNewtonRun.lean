-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_IsNewtonRun
-- name    : VBSDP_Duality_Supplement_IsNewtonRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:07:04.496036+00:00
-- url     : https://prove2.me/theorems/b1a3b47b-185b-466a-9ff1-1619ca0a22f9
-- title:
--   p. 72 — a run of the Newton method with exact line search for computing the analytic center
-- statement:
--   A sequence $x^{(0)},x^{(1)},\dots$ in $\mathbb R^m$ is a **run of the Newton method for computing the analytic center** when $x^{(0)}$ is strictly feasible ($F(x^{(0)})>0$) and, for every $k$,
--
--   1. $\delta x^N$ is the Newton direction (48) at $x^{(k)}$;
--   2. $\hat p=\operatorname{argmin}_p\phi(x^{(k)}+p\,\delta x^N)$, the minimum taken over the real $p$ with $F(x^{(k)}+p\,\delta x^N)>0$;
--   3. $x^{(k+1)}=x^{(k)}+\hat p\,\delta x^N$.
--
--   **Formalization Note** The algorithm on the page has no stopping rule ("repeat"), so a run is an infinite sequence. The exact line search minimizes over the points where $\phi$ is finite; $\hat p$ is required to be such a point. No sign restriction is placed on $\hat p$ ($p\in\mathbf R$ on p. 72). When $\mathbf X$ is bounded the line-search minimum is attained, so runs exist from every strictly feasible start.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 72 (PDF p. 24), Newton method for computing the analytic center; https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsNewtonDirection

namespace VBSDP.Duality.Supplement

/-- A run of the Newton method for computing the analytic center, p. 72: `x⁽⁰⁾` is
strictly feasible, and for every `k` the update is `x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ + p̂ δxᴺ`, where `δxᴺ` is
the Newton direction at `x⁽ᵏ⁾` and `p̂ = argmin ϕ(x⁽ᵏ⁾ + p δxᴺ)` is an exact line search
over the real `p` with `F(x⁽ᵏ⁾ + p δxᴺ) ≻ 0` (where `ϕ` is finite). -/
def IsNewtonRun {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ) (xk : ℕ → Fin m → ℝ) : Prop :=
  (VBSDP.Duality.lmi F₀ F (xk 0)).PosDef ∧
  ∀ k : ℕ, ∃ δx : Fin m → ℝ, ∃ p : ℝ,
    IsNewtonDirection F₀ F (xk k) δx ∧
    (VBSDP.Duality.lmi F₀ F (xk k + p • δx)).PosDef ∧
    (∀ p' : ℝ, (VBSDP.Duality.lmi F₀ F (xk k + p' • δx)).PosDef →
      barrier F₀ F (xk k + p • δx) ≤ barrier F₀ F (xk k + p' • δx)) ∧
    xk (k + 1) = xk k + p • δx

end VBSDP.Duality.Supplement


