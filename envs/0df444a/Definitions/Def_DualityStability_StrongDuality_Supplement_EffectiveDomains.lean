-- Prove2me | Definitions.Def_DualityStability_StrongDuality_Supplement_EffectiveDomains
-- name    : DualityStability_StrongDuality_Supplement_EffectiveDomains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:36:53.285872+00:00
-- url     : https://prove2.me/theorems/978e71c1-a736-4121-9d7d-7df4286bcd9d
-- title:
--   Effective domains $C$, $D$, $D^*$, §3, p. 171
-- statement:
--   Throughout, $E,E^*$ and $F,F^*$ are topologically paired real locally convex spaces, $A:E\to F$ is continuous linear with adjoint $A^*$, $f:E\to[-\infty,+\infty]$ is a lower semicontinuous proper convex function and $g:F\to[-\infty,+\infty]$ an upper semicontinuous proper concave function, with conjugates $f^*$ (2.2) and $g^*$ (2.5) (the published standing setting `Program`).
--
--   The **effective domains** used by the paper are
--
--   $$
--   C=\{x\in E: f(x)<+\infty\},\qquad D=\{y\in F: g(y)>-\infty\},\qquad D^*=\{y^*\in F^*: g^*(y^*)>-\infty\}.
--   $$
--
--   $C$ and $D$ carry the implicit constraints (3.1) of the primal problem, and $C\times D^*$ is the domain of the Kuhn–Tucker function of §9.
--
--   **Formalization Note** Since $f$ never takes $-\infty$ and $g$, $g^*$ never take $+\infty$ under the standing hypotheses, these sets are exactly the sets where the respective function is finite.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 171, §3 (effective domains C, D, D*)

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

/-- The effective domain `C = {x ∈ E | f(x) < +∞}` of `f` (§3, p. 171). -/
def effDomF (p : Program E E' F F') : Set E := {x | p.f x < ⊤}

/-- The effective domain `D = {y ∈ F | g(y) > -∞}` of the concave `g` (§3, p. 171). -/
def effDomG (p : Program E E' F F') : Set F := {y | ⊥ < p.g y}

/-- The effective domain `D* = {y* ∈ F* | g*(y*) > -∞}` of the concave conjugate `g*`
(§3, p. 171). -/
def effDomGstar (p : Program E E' F F') : Set F' := {y' | ⊥ < p.gstar y'}

end DualityStability.StrongDuality.Supplement


