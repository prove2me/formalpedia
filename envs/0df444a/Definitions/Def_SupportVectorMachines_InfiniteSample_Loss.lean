-- Prove2me | Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
-- name    : SupportVectorMachines_InfiniteSample_Loss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:01:44.804514+00:00
-- url     : https://prove2.me/theorems/972a2155-3442-4eed-9cf5-d4cb1f6db87b
-- title:
--   A loss function
-- statement:
--   A **loss function** (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
--   Definition 2.1, p. 22) on a measurable space $X$ and closed label set $Y \subset \mathbb R$
--   is a measurable function
--
--   $$
--   L : X \times Y \times \mathbb R \to [0,\infty).
--   $$
--
--   $L(x,y,t)$ is interpreted as the cost of predicting $y$ by the value $t = f(x)$ when $x$ is
--   observed: the smaller $L(x,y,f(x))$ is, the better $f(x)$ predicts $y$ in the sense of $L$.
--
--   This mission (Chapter 5, "Infinite-Sample Versions of Support Vector Machines") studies the
--   minimizers of the regularized risk built from a general loss of this kind, over both a
--   population distribution and a finite sample, without committing to any specific loss (hinge,
--   least-squares, etc.).
--
--   **Formalization Note** Represented as a curried function `X → ℝ → ℝ → ℝ`; the middle argument
--   ranges over all of $\mathbb R$ rather than a distinguished closed subset $Y$, and measurability
--   of $L$ is not baked into the type — both are supplied as separate hypotheses exactly where a
--   specific loss or measurability property is actually used, matching how the book itself treats
--   $L$ throughout the chapter. Restated inside this chunk's own sub-namespace rather than
--   imported from the `LossFunctions` chapter draft, per this series' cross-chapter-reuse rule
--   (drafts cannot import one another).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 22, Definition 2.1

import Mathlib

namespace SupportVectorMachines.InfiniteSample

/-- A loss function (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22, restated locally per Hard Rule 9 rather than imported from the
`LossFunctions` chapter draft): given a measurable space `X` and closed label set `Y ⊂ ℝ`, a loss
is a measurable map `L : X × Y × ℝ → [0,∞)`. Here it is represented as a curried function
`X → ℝ → ℝ → ℝ` (the middle argument ranges over the ambient reals; hypotheses fixing it to the
relevant label set `Y` and its nonnegativity are supplied where a specific loss is used, not
baked into the type). -/
abbrev Loss (X : Type*) : Type _ := X → ℝ → ℝ → ℝ

end SupportVectorMachines.InfiniteSample


