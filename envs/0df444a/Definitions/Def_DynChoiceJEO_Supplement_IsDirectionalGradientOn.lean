-- Prove2me | Definitions.Def_DynChoiceJEO_Supplement_IsDirectionalGradientOn
-- name    : DynChoiceJEO_Supplement_IsDirectionalGradientOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:12:43.183571+00:00
-- url     : https://prove2.me/theorems/6d91ba0d-b0f8-501f-a528-36450016d330
-- title:
--   Gradient selection representing the one-sided derivatives along $Z$
-- statement:
--   Let $E$ be a real normed space, $Z\subseteq E$, $f$ a real function and $\nabla f$ a map assigning to each point a continuous linear functional on $E$. The selection $\nabla f$ **represents the one-sided derivatives of $f$ along $Z$** if, for all $z,u\in Z$,
--
--   $$
--   \lim_{s\to0^+}\frac{f(z+s(u-z))-f(z)}{s}=\langle\nabla f(z),u-z\rangle .
--   $$
--
--   This holds when $f$ is differentiable within $Z$ with gradient $\nabla f$. For convex $f$ it implies that each $\nabla f(z)$ is a subgradient of $f$ at $z$ relative to $Z$; the converse fails at a kink. It is the corrected meaning of $\nabla\omega$ in Theorems 3 and 4 of the paper, which are false when $\nabla\omega$ is an arbitrary subgradient selection as the notation on p.6 allows.
--
--   **Formalization Note** The limit is written as the derivative at $s=0$ within $[0,1]$, so for convex $Z$ only the values of $f$ on $Z$ are used.
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Notation (meaning of ∇f), p.6, as used for ∇ω in Theorems 3 and 4, p.15 (corrected convention)

import Mathlib

namespace DynChoiceJEO.Supplement

/-- **A gradient selection that represents the one-sided derivatives along `Z`.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*,
arXiv:1702.05702v5, Notation, p.6: "we abuse notation slightly by denoting ∇f(x) for both the gradient of
function f at x if f is differentiable and a subgradient of f at x, even if f is not
differentiable"; used for `∇ω` in Theorems 3 and 4, p.15.

`IsDirectionalGradientOn Z f g` says that for all `z, u ∈ Z` the right derivative at `s = 0` of
`s ↦ f (z + s • (u - z))` equals `g z (u - z)`.

**Formalization Note** This is the corrected reading of `∇ω` needed by Theorems 3 and 4, which
are false for an arbitrary subgradient selection. It holds whenever `g` is the gradient of an `f`
differentiable within `Z`. When `f` is convex on `Z`, it implies that every `g z` is a subgradient
of `f` at `z` relative to `Z`. The pairing `⟨g, v⟩` is the evaluation of a continuous linear
functional. The derivative is taken within `[0, 1]`, so for convex `Z` only values of `f` on `Z`
are used. -/
def IsDirectionalGradientOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Set E) (f : E → ℝ) (g : E → E →L[ℝ] ℝ) : Prop :=
  ∀ z ∈ Z, ∀ u ∈ Z,
    HasDerivWithinAt (fun s : ℝ => f (z + s • (u - z))) (g z (u - z)) (Set.Icc 0 1) 0

end DynChoiceJEO.Supplement


