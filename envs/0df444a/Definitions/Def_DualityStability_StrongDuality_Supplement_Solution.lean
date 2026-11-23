-- Prove2me | Definitions.Def_DualityStability_StrongDuality_Supplement_Solution
-- name    : DualityStability_StrongDuality_Supplement_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:37:48.860351+00:00
-- url     : https://prove2.me/theorems/4e9936fb-c2ba-4d1a-b099-dfbfc2aa8f5e
-- title:
--   Solutions to (P) and (P*), §3, p. 173
-- statement:
--   In the standing setting of §3, consider the primal problem
--
--   $$
--   (P)\quad \text{minimize } f(x)-g(Ax) \text{ over } x\in E
--   $$
--
--   with value $\inf(P)=h(0)$, and the dual problem $(P^*)$: maximize $g^*(y^*)-f^*(A^*y^*)$ over $y^*\in F^*$, with value $\sup(P^*)$.
--
--   1. A vector $x\in E$ is a **solution to (P)** if it satisfies the implicit constraints (3.1), $x\in C$ and $Ax\in D$, and the infimum in (P) is achieved at $x$: $f(x)-g(Ax)=\inf(P)$.
--   2. A vector $y^*\in F^*$ is a **solution to (P\*)** if the supremum in $(P^*)$ is achieved at $y^*$ and is not $-\infty$: $g^*(y^*)-f^*(A^*y^*)=\sup(P^*)>-\infty$.
--
--   The paper writes $\min(P)$ and $\max(P^*)$ to indicate that the extremum is achieved. No solution to (P) is said to exist when (P) is inconsistent, even though $+\infty$ is then achieved everywhere.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 173, §3 (solutions to (P) and (P*))

import Definitions.Def_DualityStability_StrongDuality_Supplement_EffectiveDomains

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

/-- `x` is a solution to (P) (§3, p. 173): it satisfies the implicit constraints (3.1),
`x ∈ C` and `Ax ∈ D`, and the infimum of (P) is achieved at `x`. -/
def IsPrimalSolution (p : Program E E' F F') (x : E) : Prop :=
  x ∈ effDomF p ∧ p.A x ∈ effDomG p ∧ p.primalAt 0 x = p.h 0

/-- `y*` is a solution to (P*) (§3, p. 173): the supremum of (P*) is achieved at `y*`
and is not `-∞`. -/
def IsDualSolution (p : Program E E' F F') (y' : F') : Prop :=
  p.dualAt y' = p.dualValue ∧ p.dualValue ≠ ⊥

end DualityStability.StrongDuality.Supplement


