-- Prove2me | Definitions.Def_IntervalToDynamic_wrapperHistory
-- name    : IntervalToDynamic_wrapperHistory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:54.188198+00:00
-- url     : https://prove2.me/theorems/145f7e10-c61c-44cf-aa28-a252692eb9a6
-- title:
--   Algorithm 1: the history of surrogate losses
-- statement:
--   The history of Algorithm 1 after $n$ rounds is the list $[h_1,\dots,h_n]$ of surrogates fed to the inner algorithm $\mathcal A$: at round $n+1$ the algorithm $\mathcal A$ produces $y_{n+1}$ from the history, and the surrogate $h_{n+1}$ built from $y_{n+1}$ is appended.
--
--   **Formalization Note** The recursion makes the adaptivity explicit: $h_t$ depends on $y_t$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Algorithm 1, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_OnlineAlgorithm
import Definitions.Def_IntervalToDynamic_roundLoss

namespace IntervalToDynamic

/-- The history of Algorithm 1 run with inner algorithm `A` and gradient oracles `g`: the list
`[h_1, …, h_n]` of the surrogate losses fed to `A` in the first `n` rounds. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Algorithm 1, p.8.

**Formalization Note.** Round `n + 1` asks `A` for `y_{n+1}` on the history so far and appends the
loss built from it. The surrogates are therefore adaptive: `h_t` depends on `y_t`. -/
noncomputable def wrapperHistory {d : ℕ} (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (A : OnlineAlgorithm (EuclideanSpace ℝ (Fin d))) (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : ℕ → List (EuclideanSpace ℝ (Fin d) → ℝ)
  | 0 => []
  | n + 1 =>
      wrapperHistory mode X DX G A g n ++
        [roundLoss mode X DX G (g (n + 1)) (A (wrapperHistory mode X DX G A g n))]

end IntervalToDynamic


