-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_HasSpatialModulus
-- name    : ReflectedBSDE_Obstacle_HasSpatialModulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:36.159701+00:00
-- url     : https://prove2.me/theorems/0ef26d25-8e78-444e-aea6-188caf1b8969
-- title:
--   Spatial continuity condition (27)
-- statement:
--   For every radius $R>0$, the generator $f$ has a continuous nonnegative modulus $m_R$ with $m_R(0)=0$, uniform over time, bounded spatial points, bounded scalar arguments, and all gradient arguments:
--
--   $$
--   |f(t,x,r,z)-f(t,y,r,z)|\le m_R\bigl(|x-y|(1+|z|)\bigr)
--   $$
--
--   whenever $t\in[0,T]$, $|x|,|y|,|r|\le R$. This is the extra assumption used only for comparison and uniqueness.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 731, equation (27)

import Definitions.Def_ReflectedBSDE_Obstacle_Data

open MeasureTheory Filter Topology
open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Condition (27): local spatial continuity of the generator, with a modulus
that is continuous at zero and is uniform in time, scalar value and gradient. -/
def HasSpatialModulus {d : ℕ} (D : Data d) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ m : ℝ → ℝ,
    ContinuousOn m (Set.Ici 0) ∧ m 0 = 0 ∧
    (∀ s : ℝ, 0 ≤ s → 0 ≤ m s) ∧
    ∀ t ≤ D.T, ∀ x y : Fin d → ℝ, ∀ r : ℝ, ∀ z : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → |r| ≤ R →
      |D.f t x r z - D.f t y r z| ≤ m (‖x - y‖ * (1 + ‖z‖))

end ReflectedBSDE.Obstacle


