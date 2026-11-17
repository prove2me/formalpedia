-- Prove2me | Definitions.Def_QGChasing_Supplement_sqOpt
-- name    : QGChasing_Supplement_sqOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:26:34.47407+00:00
-- url     : https://prove2.me/theorems/b3df25dc-166e-4d38-8e01-44211ea5993a
-- title:
--   Offline optimum $\mathrm{OPT}_T$ under squared movement
-- statement:
--   For hitting costs $f_1,\dots,f_T$ on $\mathbb R^d$, a start $x_0$ and a horizon $T$, the offline optimum is
--   $$
--   \mathrm{OPT}_T=\inf\Big\{\sum_{t=1}^T\Big(f_t(u_t)+\frac12\|u_t-u_{t-1}\|^2\Big)\ :\ u_1,\dots,u_T\in\mathbb R^d,\ u_0=x_0\Big\}.
--   $$
--   This is the denominator of the competitive ratio when the decision set is all of $\mathbb R^d$, as in the lower bound.
--
--   **Formalization Note** For nonnegative $f_t$ the set is bounded below by $0$, so the infimum is a genuine real infimum.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), p.1 (denominator of CR); Lemma 5.3, p.12 (OPT_T)

import Mathlib
import Definitions.Def_QGChasing_Supplement_sqCost

namespace QGChasing.Supplement

/-- The offline optimum `OPT_T = inf_{u₁, …, u_T ∈ ℝᵈ} ∑_{t=1}^T (f_t(u_t) + ½‖u_t − u_{t−1}‖²)` with
`u₀ = x₀` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.1, denominator of `CR` with `X = ℝᵈ`; Lemma 5.3, p.12, `OPT_T`).

**Formalization Note** The infimum of `sqCost f u T` over all sequences `u` with `u 0 = x₀` (only
`u 1, …, u T` enter the cost). The set is nonempty; when the costs `f_t` are nonnegative (as in every
use) it is bounded below by `0`, so the infimum is a genuine real infimum. -/
noncomputable def sqOpt {d : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  sInf ((fun u : ℕ → EuclideanSpace ℝ (Fin d) => sqCost f u T) '' {u | u 0 = x₀})

end QGChasing.Supplement


