-- Prove2me | Definitions.Def_WassTwoStage_LP1_Gauge
-- name    : WassTwoStage_LP1_Gauge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:54:50.43835+00:00
-- url     : https://prove2.me/theorems/a063e058-f085-4c05-b659-2562e696b012
-- title:
--   The asymmetric reference gauge (31) $\|\xi\| = e^\top\max\{w_+\xi, -w_-\xi\}$, its dual norm and transport cost
-- statement:
--   Fix a dimension $K$ and two scaling parameters $w_+, w_- \in \mathbb R$ (positive in every use). For $\xi \in \mathbb R^K$ define
--
--   $$\|\xi\| \;=\; e^\top \max\{w_+\cdot\xi,\; -w_-\cdot\xi\} \;=\; \sum_{k\in[K]} \max\{w_+\xi_k,\; -w_-\xi_k\}, \qquad (31)$$
--
--   where $e$ is the all-ones vector and the maximum is taken componentwise. Three objects are built from it.
--
--   1. The **gauge** $\|\cdot\|$ itself. For $w_+ = w_- = 1$ it is the 1-norm; for $w_+ \neq w_-$ it is positively homogeneous, subadditive and positive off the origin, but not symmetric: moving in the positive direction of a coordinate costs $w_+$ per unit, moving in the negative direction costs $w_-$ per unit.
--   2. The **dual norm** (polar gauge)
--   $$\|z\|_* \;=\; \sup\{\, z^\top\xi \;:\; \xi\in\mathbb R^K,\ \|\xi\|\le 1 \,\},$$
--   an extended real number (finite when $w_+, w_- > 0$).
--   3. The **transport cost** $d(\xi,\xi') = \|\xi - \xi'\|$, viewed as a $[0,\infty]$-valued function. The first argument is the point of the perturbed distribution and the second the point of the empirical distribution, as in $d(\xi,\hat\xi_i) = \|\xi-\hat\xi_i\|$.
--
--   These are the reference distance of the 1-Wasserstein ambiguity set of Section 4 of Hanasusanto and Kuhn, and the dual norm used in the proof of Theorem 6.
--
--   **Formalization Note** The supremum defining $\|z\|_*$ is taken in the extended reals, so no default value is substituted for an unbounded set. The transport cost is the nonnegative part of the gauge (`ENNReal.ofReal`); for $w_+, w_- > 0$ the gauge is already nonnegative.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 22, (31); p. 23 (dual norm, proof of Theorem 6)

import Mathlib

open Matrix

namespace WassTwoStage.LP1

/-- The reference "norm" (31) of Hanasusanto–Kuhn, *Conic Programming Reformulations of
Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls*, arXiv:1609.07505v3,
p. 22: `‖ξ‖ = eᵀ max{w₊ · ξ, −w₋ · ξ} = Σ_{k ∈ [K]} max{w₊ ξ_k, −w₋ ξ_k}` for positive scaling
parameters `w₊ = wp` and `w₋ = wm`. For `w₊ ≠ w₋` this is a gauge (positively homogeneous,
subadditive, positive off `0`) but not symmetric: `‖−ξ‖ ≠ ‖ξ‖` in general. For `w₊ = w₋ = 1` it
is the 1-norm. -/
noncomputable def gauge {K : ℕ} (wp wm : ℝ) (ξ : Fin K → ℝ) : ℝ :=
  ∑ k, max (wp * ξ k) (-(wm * ξ k))

/-- The dual norm of (31), defined as the polar of the gauge, as the paper's proof of Theorem 6
uses it ("invoking the definition of the dual norm", p. 23):
`‖z‖_* = sup {zᵀξ : ξ ∈ ℝ^K, ‖ξ‖ ≤ 1}`, an extended real number (the supremum is never taken in
`ℝ`, so no junk value arises; for `w₊, w₋ > 0` it is finite). -/
noncomputable def dualGauge {K : ℕ} (wp wm : ℝ) (z : Fin K → ℝ) : EReal :=
  ⨆ (ξ : Fin K → ℝ) (_ : gauge wp wm ξ ≤ 1), ((z ⬝ᵥ ξ : ℝ) : EReal)

/-- The transport cost of the 1-Wasserstein ball of §4 (p. 22): `d(ξ, ξ') = ‖ξ − ξ'‖` with the
gauge (31), as a `[0, ∞]`-valued function. The first argument `ξ` is the point of the perturbed
distribution `ℙ` and the second `ξ'` the point of the empirical distribution `ℙ̂_I`, matching
`d(ξ, ξ̂_i) = ‖ξ − ξ̂_i‖` in Theorem 1 (6) and in the proof of Theorem 6. -/
noncomputable def gaugeCost {K : ℕ} (wp wm : ℝ) (ξ ξ' : Fin K → ℝ) : ENNReal :=
  ENNReal.ofReal (gauge wp wm (ξ - ξ'))

end WassTwoStage.LP1


