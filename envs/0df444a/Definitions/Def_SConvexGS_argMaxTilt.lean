-- Prove2me | Definitions.Def_SConvexGS_argMaxTilt
-- name    : SConvexGS_argMaxTilt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:22.271584+00:00
-- url     : https://prove2.me/theorems/c4c153cd-5973-417b-8d5d-1bfcb1b4a389
-- title:
--   Maximizers $\arg\max f[-p]$
-- statement:
--   For $f:\mathbb R^n\to[-\infty,\infty)$ and $p\in\mathbb R^n$, write $f[-p](x)=f(x)-p^{T}x$. Then
--
--   $$\arg\max f[-p]=\{x\in\mathbb R^n\mid f(z)-p^{T}z\le f(x)-p^{T}x\ \text{ for all } z\in\mathbb R^n\}.$$
--
--   Read as a valuation $f$ at prices $p$, this set is the agent's demand.
--
--   **Formalization Note** There is no clause $x\in\operatorname{dom}(f)$. When $\operatorname{dom}(f)\ne\emptyset$ a maximizer lies in $\operatorname{dom}(f)$ anyway. When $f\equiv-\infty$ every point is a maximizer, the reading under which Corollary 2 holds as printed.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9, and Definition 3, p.21

import Mathlib

open Matrix

namespace SConvexGS

/-- The set `arg max f[−p]` of maximizers of `f[−p](x) = f(x) − pᵀx` over ℝⁿ (Chen, Li,
*S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9, and
Definition 3, p.21).

Formalization Note: `xᵀy` is `x ⬝ᵥ y`. There is no clause `x ∈ dom f`. If `dom f ≠ ∅` and `f < ∞`
then a maximizer lies in `dom f` anyway, so the clause would change nothing. If `f ≡ −∞` every
point is a maximizer, which is the reading under which Corollary 2 holds as printed. -/
def argMaxTilt {n : ℕ} (f : (Fin n → ℝ) → EReal) (p : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ z, f z - ((p ⬝ᵥ z : ℝ) : EReal) ≤ f x - ((p ⬝ᵥ x : ℝ) : EReal)}

end SConvexGS


