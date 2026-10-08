-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_penalty
-- name    : ReflectedBSDE_Obstacle_penalty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:55.959736+00:00
-- url     : https://prove2.me/theorems/fe7005e8-b568-4fd0-aabe-1cba1d283787
-- title:
--   Doubled-variable comparison function
-- statement:
--   For functions $u$ and $v$ and a parameter $\alpha>0$, define the doubled-variable comparison function
--
--   $$
--   \Phi_\alpha(t,x,y)=u(t,x)-v(t,y)-\frac{\alpha}{2}|x-y|^2.
--   $$
--
--   Its maximizers are the objects analyzed by Lemma 8.7. The squared norm here is the Euclidean sum of coordinate squares.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 733, proof of Theorem 8.6 before Lemma 8.7

import Mathlib

open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- The doubled-variable function Φ_α in the proof of Theorem 8.6. -/
noncomputable def penalty {d : ℕ}
    (u v : ℝ≥0 → (Fin d → ℝ) → ℝ) (α : ℝ)
    (t : ℝ≥0) (x y : Fin d → ℝ) : ℝ :=
  u t x - v t y - (α / 2) * ∑ i, (x i - y i) ^ 2

end ReflectedBSDE.Obstacle


