-- Prove2me | Definitions.Def_TeschlODE_Horseshoe_horseshoeInv
-- name    : TeschlODE_Horseshoe_horseshoeInv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:52:01.258813+00:00
-- url     : https://prove2.me/theorems/8da31694-78bd-45f7-a378-6d950b433c66
-- title:
--   The inverse $g = f^{-1}$ of the horseshoe map on $K_0, K_1$ (13.5)–(13.6)
-- statement:
--   With $K_0 = f(J_0) = [0, \lambda] \times [0, 1]$ and $K_1 = f(J_1) = [1 - \lambda, 1] \times [0, 1]$, the inverse of the horseshoe map is
--   $$g(x, y) = (\lambda^{-1} x, \mu^{-1} y) \text{ on } K_0, \qquad g(x, y) = (\lambda^{-1}(1 - x), 1 - \mu^{-1} y) \text{ on } K_1.$$
--
--   **Formalization Note.** Implemented as "first formula if $x \le \lambda$, second otherwise". For $\lambda < 1/2$ the strips $K_0$, $K_1$ are disjoint, so on $K_0 \cup K_1$ this is the book's $g$. The values elsewhere carry no meaning.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 332, §13.1, Eqs. (13.5)–(13.6)

import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, p. 332, (13.5)–(13.6): the inverse `g = f⁻¹` of the horseshoe map on
`K₀ = f(J₀) = [0, λ] × [0, 1]` and `K₁ = f(J₁) = [1 − λ, 1] × [0, 1]`:
`g(x, y) = (λ⁻¹x, µ⁻¹y)` on `K₀` (13.5) and `g(x, y) = (λ⁻¹(1 − x), 1 − µ⁻¹y)` on `K₁` (13.6).
Here the first formula is used whenever `x ≤ λ` and the second otherwise; for `λ < 1/2` the
strips `K₀`, `K₁` are disjoint, and the values off `K₀ ∪ K₁` carry no meaning. -/
noncomputable def horseshoeInv (lam μ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if p.1 ≤ lam then (lam⁻¹ * p.1, μ⁻¹ * p.2) else (lam⁻¹ * (1 - p.1), 1 - μ⁻¹ * p.2)

end TeschlODE.Horseshoe


