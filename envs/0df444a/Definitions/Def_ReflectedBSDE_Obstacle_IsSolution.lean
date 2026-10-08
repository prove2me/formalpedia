-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_IsSolution
-- name    : ReflectedBSDE_Obstacle_IsSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:44.12222+00:00
-- url     : https://prove2.me/theorems/015d68ac-e4a9-42f6-9934-cd0db039e965
-- title:
--   Viscosity solution of the obstacle problem
-- statement:
--   A viscosity solution of the obstacle problem is simultaneously a viscosity subsolution and a viscosity supersolution. Consequently it obeys the terminal equality and both interior jet inequalities:
--
--   $$
--   u(T,x)=g(x),\qquad u\text{ satisfies the superjet and subjet tests of Definition 8.3.}
--   $$
--
--   This predicate is the solution notion in the uniqueness theorem.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 729, Definition 8.3(c)

import Definitions.Def_ReflectedBSDE_Obstacle_IsSubsolution
import Definitions.Def_ReflectedBSDE_Obstacle_IsSupersolution

open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Definition 8.3(c): a continuous viscosity solution satisfies both
jet inequalities and both terminal inequalities. -/
def IsSolution {d : ℕ} (D : Data d)
    (u : ℝ≥0 → (Fin d → ℝ) → ℝ) : Prop :=
  IsSubsolution D u ∧ IsSupersolution D u

end ReflectedBSDE.Obstacle


