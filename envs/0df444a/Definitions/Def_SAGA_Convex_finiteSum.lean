-- Prove2me | Definitions.Def_SAGA_Convex_finiteSum
-- name    : SAGA_Convex_finiteSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:10:59.607897+00:00
-- url     : https://prove2.me/theorems/15b19fec-f6e0-4c06-832a-df7dae34fefe
-- title:
--   The finite-sum objective $f=\frac1n\sum_i f_i$ and the averaged gradient
-- statement:
--   Let $n\ge 1$ and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be the component functions of a finite-sum problem, with given vector fields $f_1',\dots,f_n':\mathbb R^d\to\mathbb R^d$ (the component gradients). The **finite-sum objective** and its **averaged gradient** are
--
--   $$
--   f(x)=\frac1n\sum_{i=1}^n f_i(x),\qquad f'(x)=\frac1n\sum_{i=1}^n f_i'(x).
--   $$
--
--   These are the objective $f$ of Defazio, Bach and Lacoste-Julien and its gradient $f'$, used by every statement of the mission.
--
--   **Formalization Note** The components are indexed by `Fin n` (0-based). `fAvg f x` is $f(x)$ and `gradAvg f' x` is $f'(x)$; the space is `EuclideanSpace ℝ (Fin d)`. That $f_i'$ is the gradient of $f_i$ is a hypothesis of each theorem (`HasGradientAt`), not part of the definition.
-- source:
--   Defazio, Bach & Lacoste-Julien, SAGA, arXiv:1407.0202v3, p. 1, Section 1 (definition of f)

import Mathlib

namespace SAGA.Convex

/-- The finite-sum objective `f(x) = (1/n) ∑ᵢ fᵢ(x)` (Defazio–Bach–Lacoste-Julien, p. 1),
with the components indexed by `Fin n`. -/
noncomputable def fAvg {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i x

/-- The average `f′(x) = (1/n) ∑ᵢ f′ᵢ(x)` of the given component gradients `f′ᵢ`. -/
noncomputable def gradAvg {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (1 / (n : ℝ)) • ∑ i, f' i x

end SAGA.Convex


