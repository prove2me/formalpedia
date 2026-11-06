-- Prove2me | Definitions.Def_AnchoredEP_tangentResidual
-- name    : AnchoredEP_tangentResidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:55.099554+00:00
-- url     : https://prove2.me/theorems/2eec2f17-eb98-4b11-979c-3d070a6b4fb1
-- title:
--   Tangent residual $\mathrm{res}^{\tan}(z)$
-- statement:
--   For $F:\mathbb R^d\to\mathbb R^d$ and a set-valued $H:\mathbb R^d\rightrightarrows\mathbb R^d$, the **tangent residual** of a point $z$ is
--   $$
--   \mathrm{res}^{\tan}(z)=\inf_{v\in H(z)}\|F(z)+v\|=\operatorname{dist}\big(0,F(z)+H(z)\big).
--   $$
--   Every $v\in H(z)$ gives the computable upper bound $\mathrm{res}^{\tan}(z)\le\|F(z)+v\|$. The tangent residual reduces to the gradient norm when $H=0$ and bounds the duality gap and other optimality measures.
--
--   **Formalization Note** The infimum is a real infimum, which Lean evaluates to $0$ on an empty set (where the source's value is $+\infty$). The theorems of this mission therefore always state a certificate $v\in H(z)$, $\|F(z)+v\|\le\varepsilon$ alongside any bound on the tangent residual.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 2, Eq. (2), p.3

import Mathlib

namespace AnchoredEP

/-- **Tangent residual.** Jiang–Yoon, arXiv:2609.30212, Section 2, Eq. (2), p.3:
`res^tan(z) := inf_{v ∈ H(z)} ‖F(z) + v‖ = dist(0, F(z) + H(z))`. Any `v ∈ H(z)` gives the
computable upper bound `res^tan(z) ≤ ‖F(z) + v‖`.

**Formalization Note.** The infimum is the real `sInf` of the image of `H z` under
`v ↦ ‖F z + v‖`. When `H z = ∅` Lean's `sInf ∅ = 0` (the source's value is `+∞`); the theorems of
this mission therefore never state a conclusion as `tangentResidual … ≤ ε` alone, but always
together with a certificate `v ∈ H z ∧ ‖F z + v‖ ≤ ε`. -/
noncomputable def tangentResidual {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf ((fun v => ‖F z + v‖) '' H z)

end AnchoredEP


