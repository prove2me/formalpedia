-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_IsSupersolution
-- name    : ReflectedBSDE_Obstacle_IsSupersolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:13.026985+00:00
-- url     : https://prove2.me/theorems/966320e5-1ec1-4d6a-b179-458a16561850
-- title:
--   Viscosity supersolution of the obstacle problem
-- statement:
--   A continuous function $u$ is a viscosity supersolution if $u(T,x)\ge g(x)$ for all $x$ and, at every interior point and every parabolic subjet $(p,q,X)$,
--
--   $$
--   \min\{u(t,x)-h(t,x),\;-p-\tfrac12\operatorname{Tr}(aX)-b\cdot q-f(t,x,u(t,x),q\sigma)\}\ge0,
--   $$
--
--   where $a=\sigma\sigma^\top$. This is the lower jet inequality in the obstacle problem.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), pp. 728–729, Definition 8.3(b)

import Definitions.Def_ReflectedBSDE_Obstacle_obstacleOperator
import Definitions.Def_ReflectedBSDE_Obstacle_Subjet

open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Definition 8.3(b), including the terminal lower bound. -/
def IsSupersolution {d : ℕ} (D : Data d)
    (u : ℝ≥0 → (Fin d → ℝ) → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ≥0 × (Fin d → ℝ) => u z.1 z.2)
    (Set.Icc 0 D.T ×ˢ Set.univ) ∧
  (∀ x, D.g x ≤ u D.T x) ∧
  ∀ t : ℝ≥0, ∀ x : Fin d → ℝ, ∀ j : Jet d,
    Subjet D.T u t x j → 0 ≤ min (u t x - D.h t x) (obstacleOperator D u t x j)

end ReflectedBSDE.Obstacle


