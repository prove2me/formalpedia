-- Prove2me | Definitions.Def_IntervalToDynamic_correctedGrad
-- name    : IntervalToDynamic_correctedGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:46.079594+00:00
-- url     : https://prove2.me/theorems/75c3f4dd-a72c-4f85-b5c9-0c37b2f0a99a
-- title:
--   Algorithm 1: the corrected gradient $d_t$
-- statement:
--   For $g,n\in\mathbb R^d$, the corrected gradient is
--   $$
--   d=g+\frac{\max\{-g^\top n,0\}}{\|n\|_2^2}\,n,
--   $$
--   with the convention $d=g$ for $n=0$. In Algorithm 1, $g=g_t$ is the observed gradient and $n=n_t=y_t-x_t$ the projection residual.
--
--   The correction removes the component of $g$ against the residual, so that a loss on the domain $\mathcal X$ can be transferred to the larger domain $\mathcal Y$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib

namespace IntervalToDynamic

open Classical in
/-- The corrected gradient of Algorithm 1. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Algorithm 1, p.8:
`d_t = g_t + (max{−g_tᵀ n_t, 0} / ‖n_t‖₂²) n_t`, with the convention `d_t = g_t` for `n_t = 0`. -/
noncomputable def correctedGrad {d : ℕ} (g n : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if n = 0 then g else g + (max (-(inner ℝ g n)) 0 / ‖n‖ ^ 2) • n

end IntervalToDynamic


