-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_PolynomialGrowth
-- name    : ReflectedBSDE_Obstacle_PolynomialGrowth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:51.926457+00:00
-- url     : https://prove2.me/theorems/b433828c-b69f-4af5-83f6-953afb3ad592
-- title:
--   Uniform polynomial growth
-- statement:
--   A function $u$ on $[0,T]\times\mathbb R^d$ has at most polynomial growth at spatial infinity if some $C\ge0$ and integer $k$ satisfy, uniformly over time,
--
--   $$
--   |u(t,x)|\le C(1+|x|^k),\qquad t\in[0,T],\ x\in\mathbb R^d.
--   $$
--
--   This is the solution class in Theorem 8.6.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 731, Theorem 8.6, growth class

import Mathlib

open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Uniform polynomial growth at spatial infinity on the closed time strip. -/
def PolynomialGrowth {d : ℕ} (T : ℝ≥0)
    (u : ℝ≥0 → (Fin d → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ,
    ∀ t ≤ T, ∀ x : Fin d → ℝ, |u t x| ≤ C * (1 + ‖x‖ ^ k)

end ReflectedBSDE.Obstacle


