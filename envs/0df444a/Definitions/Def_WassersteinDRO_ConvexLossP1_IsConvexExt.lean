-- Prove2me | Definitions.Def_WassersteinDRO_ConvexLossP1_IsConvexExt
-- name    : WassersteinDRO_ConvexLossP1_IsConvexExt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:45.815544+00:00
-- url     : https://prove2.me/theorems/fd57393d-c536-437d-867d-30a84ad8d5cd
-- title:
--   Convexity of an extended real-valued function (epigraph convexity)
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space (the paper's $\mathbb R^m$ with an arbitrary norm). A function $\ell : E \to [-\infty, +\infty]$ is **convex** if its epigraph
--   $$\operatorname{epi} \ell = \{(\xi, t) \in E \times \mathbb R : \ell(\xi) \le t\}$$
--   is a convex subset of $E \times \mathbb R$.
--
--   This is the standard notion of convexity for extended real-valued functions (Rockafellar, *Convex Analysis*, §4). It is the convexity hypothesis on the loss function in Theorem 10 of the paper, where the loss may take the values $\pm\infty$.
--
--   **Formalization Note** Mathlib's `ConvexOn` requires an ordered $\mathbb R$-module as codomain, which `EReal` is not, so convexity is stated through the epigraph. For a real-valued function it coincides with ordinary convexity on $E$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 10, p. 14 ("the loss function ℓ(ξ) is convex"); §1, p. 1 (extended real-valued loss)

import Mathlib

namespace WassersteinDRO.ConvexLossP1

/-- **Convexity of an extended real-valued loss function (epigraph convexity).**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 10, p. 14 ("the loss function ℓ(ξ) is convex"); the loss is "a measurable extended
real-valued loss function ℓ(ξ)" (§1, p. 1).

`IsConvexExt ℓ` says that the epigraph `{(ξ, t) ∈ E × ℝ : ℓ ξ ≤ t}` of `ℓ : E → EReal` is a
convex subset of `E × ℝ`. This is the standard meaning of convexity for a function with values in
`[−∞, +∞]` (Rockafellar, *Convex Analysis*, §4).

**Formalization Note.** Mathlib's `ConvexOn` needs a codomain that is an ordered `ℝ`-module, which
`EReal` is not, so convexity is stated through the epigraph. For a real-valued `ℓ` it agrees with
`ConvexOn ℝ Set.univ ℓ`. The space `(ℝ^m, ‖·‖)` of the paper is a finite-dimensional real normed
space `E`. -/
def IsConvexExt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : E → EReal) : Prop :=
  Convex ℝ {q : E × ℝ | ℓ q.1 ≤ (q.2 : EReal)}

end WassersteinDRO.ConvexLossP1


