-- Prove2me | Definitions.Def_DualityStability_StrongDuality_Supplement_Extremality
-- name    : DualityStability_StrongDuality_Supplement_Extremality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:43:18.274791+00:00
-- url     : https://prove2.me/theorems/ef21b0a8-be9a-4b4e-a89c-54bffcfaa813
-- title:
--   Extremality conditions (8.5), p. 184
-- statement:
--   In the standing setting of §3:
--
--   1. For $y^*\in F^*$, the **sub-differential** of the concave function $g^*$ at $y^*$ is the set of $y\in F$ such that
--   $$
--   g^*(y^*+w)\le g^*(y^*)+\langle y,w\rangle\quad\text{for all } w\in F^*,
--   $$
--   the concave counterpart of (2.3).
--   2. For $x\in E$, $\partial f(x)$ is the sub-differential (2.3) of the convex function $f$: the set of $x^*\in E^*$ with $f(x+z)\ge f(x)+\langle z,x^*\rangle$ for all $z\in E$.
--   3. A pair $x\in E$, $y^*\in F^*$ satisfies the **extremality conditions** (8.5) for (P) and (P\*) if
--   $$
--   Ax\in\partial g^*(y^*)\quad\text{and}\quad A^*y^*\in\partial f(x).
--   $$
--
--   By (8.3)–(8.4) these are equivalent to $f(x)+f^*(A^*y^*)\le\langle x,A^*y^*\rangle$ and $g(Ax)+g^*(y^*)\ge\langle Ax,y^*\rangle$. For dual linear programs they are the complementary slackness conditions.
--
--   **Formalization Note** $\partial f$ is the published `subdiff`; values are in `EReal`.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 184, (8.3)–(8.5); p. 170, (2.3)

import Definitions.Def_DualityStability_StrongDuality_Program

namespace DualityStability.StrongDuality.Supplement

open DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- The sub-differential `∂g*(y*) ⊆ F` of the concave function `g*` at `y*` (the concave
version of (2.3), p. 170): `y ∈ ∂g*(y*)` iff `g*(y* + w) ≤ g*(y*) + ⟨y, w⟩` for all `w ∈ F*`. -/
def gstarSubdiff (p : Program E E' F F') (y' : F') : Set F :=
  {y | ∀ w : F', p.gstar (y' + w) ≤ p.gstar y' + (p.fPair.pair y w : EReal)}

/-- The extremality conditions (8.5), p. 184: `Ax ∈ ∂g*(y*)` and `A*y* ∈ ∂f(x)`. -/
def Extremal (p : Program E E' F F') (x : E) (y' : F') : Prop :=
  p.A x ∈ gstarSubdiff p y' ∧ p.Astar y' ∈ subdiff p.ePair p.f x

end DualityStability.StrongDuality.Supplement


