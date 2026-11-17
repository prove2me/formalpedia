-- Prove2me | Definitions.Def_QGChasing_Supplement_expSqCost
-- name    : QGChasing_Supplement_expSqCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:27:19.073126+00:00
-- url     : https://prove2.me/theorems/282abb41-eda3-4c02-b05e-59d7107d8c23
-- title:
--   Expected cost $\mathbb E_\xi[\mathrm{ALG}_T]$ of a randomized algorithm
-- statement:
--   For a randomized online algorithm with seed law $P$, requests $f$ and horizon $T$, the expected cost is
--   $$
--   \mathbb E_\xi[\mathrm{ALG}_T]=\mathbb E_{\omega\sim P}\Big[\sum_{t=1}^T\Big(f_t(x_t)+\frac12\|x_t-x_{t-1}\|^2\Big)\Big],
--   $$
--   the expectation over the algorithm's internal randomness of its total cost under squared Euclidean movement.
--
--   **Formalization Note** A lower Lebesgue integral of the nonnegative part of the cost, valued in $[0,\infty]$. For nonnegative costs nothing is lost, and a cost with divergent expectation counts as $+\infty$, not $0$.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Lemma 5.3, p.12

import Mathlib
import Definitions.Def_QGChasing_Supplement_sqCost

namespace QGChasing.Supplement

/-- The expected cost `E_ξ[ALG_T]` of a randomized online algorithm on the requests `f` over horizon
`T`, with squared Euclidean movement (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), Lemma 5.3, p.12): the expectation over the seed `ω ∼ P`
of `∑_{t=1}^T (f_t(x_t) + ½‖x_t − x_{t−1}‖²)`.

**Formalization Note** A lower Lebesgue integral `∫⁻` of `ENNReal.ofReal` of the cost, valued in
`[0, ∞]`. For nonnegative costs (as in every use) `ofReal` loses nothing, and a cost whose expectation
diverges counts as `∞` rather than `0` (which a Bochner integral would return). -/
noncomputable def expSqCost {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (x : Ω → (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → ℕ → EuclideanSpace ℝ (Fin d))
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (T : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (sqCost f (x ω f) T) ∂P

end QGChasing.Supplement


