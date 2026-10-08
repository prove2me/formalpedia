-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_IsSubsolution
-- name    : ReflectedBSDE_Obstacle_IsSubsolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:06.215988+00:00
-- url     : https://prove2.me/theorems/96e074e9-193d-4302-a19b-35c206ba9203
-- title:
--   Viscosity subsolution of the obstacle problem
-- statement:
--   A continuous function $u$ is a viscosity subsolution if $u(T,x)\le g(x)$ for all $x$ and, at every interior point and every parabolic superjet $(p,q,X)$,
--
--   $$
--   \min\{u(t,x)-h(t,x),\;-p-\tfrac12\operatorname{Tr}(aX)-b\cdot q-f(t,x,u(t,x),q\sigma)\}\le0,
--   $$
--
--   where $a=\sigma\sigma^\top$. The terminal condition and interior jet tests are both part of the definition.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 728, Definition 8.3(a)

import Definitions.Def_ReflectedBSDE_Obstacle_obstacleOperator
import Definitions.Def_ReflectedBSDE_Obstacle_Superjet

open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Definition 8.3(a), including the terminal upper bound. The obstacle
inequality is tested only at interior times, as in the paper. -/
def IsSubsolution {d : ℕ} (D : Data d)
    (u : ℝ≥0 → (Fin d → ℝ) → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ≥0 × (Fin d → ℝ) => u z.1 z.2)
    (Set.Icc 0 D.T ×ˢ Set.univ) ∧
  (∀ x, u D.T x ≤ D.g x) ∧
  ∀ t : ℝ≥0, ∀ x : Fin d → ℝ, ∀ j : Jet d,
    Superjet D.T u t x j → min (u t x - D.h t x) (obstacleOperator D u t x j) ≤ 0

end ReflectedBSDE.Obstacle


