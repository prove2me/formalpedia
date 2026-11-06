-- Prove2me | Definitions.Def_QGChasing_IsCPDRun
-- name    : QGChasing_IsCPDRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:14.164307+00:00
-- url     : https://prove2.me/theorems/ef1fd8c9-02de-4071-a73e-3f1ef3d361da
-- title:
--   A trajectory of Clipped Proximal Descent
-- statement:
--   Let $\kappa\ge1$, $X\subseteq\mathbb R^d$ and hitting costs $f_1,f_2,\dots$. A sequence $x_0,x_1,x_2,\dots$ is **a run of CPD** if $x_0\in X$ (the input of Algorithm 1) and, for every round $t\ge1$, $x_t$ is the CPD decision computed from $x_{t-1}$ and $f_t$ (Algorithm 1, lines 2–7).
--
--   **Formalization Note** Rounds are indexed $t+1$ for $t\in\mathbb N$; the value $f_0$ is never used.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Algorithm 1, p.5

import Mathlib
import Definitions.Def_QGChasing_IsCPDStep

namespace QGChasing

/-- `x` is a trajectory of Clipped Proximal Descent (Algorithm 1, He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.5) on the decision set
`X` with hitting costs `f₁, f₂, …`: the initial decision `x₀` lies in `X`, and for every round
`t ≥ 1` the decision `x_t` is the CPD step from `x_{t−1}` on `f_t`.

**Formalization Note** Rounds are indexed `t + 1` for `t : ℕ`; `f 0` is never used (the paper's
rounds start at `t = 1`). -/
def IsCPDRun {d : ℕ} (κ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  x 0 ∈ X ∧ ∀ t : ℕ, IsCPDStep κ X (f (t + 1)) (x t) (x (t + 1))

end QGChasing


