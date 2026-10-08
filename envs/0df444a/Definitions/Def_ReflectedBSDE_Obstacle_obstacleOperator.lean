-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_obstacleOperator
-- name    : ReflectedBSDE_Obstacle_obstacleOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:17.264042+00:00
-- url     : https://prove2.me/theorems/79532ac2-bd9c-40d8-8f0c-25a1ea22820e
-- title:
--   The obstacle differential expression
-- statement:
--   For a jet $(p,q,X)$ at $(t,x)$, the obstacle problem uses the expression
--
--   $$
--   -p-\tfrac12\operatorname{Tr}((\sigma\sigma^\top)X)-b(t,x)\cdot q-f(t,x,u(t,x),q\sigma(t,x)).
--   $$
--
--   Here $q\sigma$ is the row vector whose $k$th coordinate is $\sum_i q_i\sigma_{ik}$. This expression is paired with $u-h$ in the viscosity inequalities.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), pp. 727–728, equation (24) and Definition 8.3

import Definitions.Def_ReflectedBSDE_Obstacle_Data
import Definitions.Def_ReflectedBSDE_Obstacle_Jet

open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- The differential expression in (24), evaluated at a parabolic jet.
The diffusion term is Tr((σσᵀ)X)/2 and the last argument of f is the
row vector qσ. -/
noncomputable def obstacleOperator {d : ℕ} (D : Data d)
    (u : ℝ≥0 → (Fin d → ℝ) → ℝ) (t : ℝ≥0) (x : Fin d → ℝ) (j : Jet d) : ℝ :=
  -j.p - (1 / 2 : ℝ) *
    (∑ i, ∑ k, (∑ l, D.sigma t x i l * D.sigma t x k l) * j.X k i) -
    (∑ i, D.b t x i * j.q i) -
    D.f t x (u t x) (fun k => ∑ i, j.q i * D.sigma t x i k)

end ReflectedBSDE.Obstacle


