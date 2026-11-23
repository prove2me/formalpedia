-- Prove2me | Definitions.Def_DualityStability_StrongDuality_Supplement_Normal
-- name    : DualityStability_StrongDuality_Supplement_Normal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:41:44.600436+00:00
-- url     : https://prove2.me/theorems/08073f14-2e24-44c3-847f-2212257923db
-- title:
--   Normality of (P) and of (P*), (6.4), p. 181
-- statement:
--   In the standing setting of §3, let $h(z)=\inf(P(z))=\inf_x\{f(x)-g(Ax-z)\}$ be the perturbation function of (P), $z\in F$.
--
--   1. (P) is **normal** if
--   $$
--   \inf(P)=\liminf_{z\to0}\,[\inf(P(z))],
--   $$
--   that is, $h$ is lower semicontinuous at $0$, where $\liminf_{z\to0}h(z)$ is the lower limit (2.1) over all $z$ near $0$, $z=0$ included.
--   2. (P\*) is **normal** in the dual manner: its minimization form $(P')$, minimize $-g^*(y^*)+f^*(A^*y^*)$ over $y^*\in F^*$, is normal, i.e. the perturbation function $h'(w)=\inf_{y^*}\{-g^*(y^*)+f^*(A^*y^*-w)\}$, $w\in E^*$, is lower semicontinuous at $0$. Equivalently, $\sup(P^*)=\limsup_{w\to0}\sup_{y^*}\{g^*(y^*)-f^*(A^*y^*-w)\}$.
--
--   Normality is the condition under which Theorem 7 gives $\inf(P)=\sup(P^*)$.
--
--   **Formalization Note** $h'$ is the published `Program.dualH`. The lower limit is `Filter.liminf` over the full neighbourhood filter `nhds 0`.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 181, (6.4); p. 173, (P′)

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

/-- (P) is normal, (6.4), p. 181: `inf (P) = lim inf_{z → 0} inf (P(z))`, i.e. the
perturbation function `h` is lower semicontinuous at `0` (lim inf over the full
neighbourhood filter, as in (2.1)). -/
def PrimalNormal (p : Program E E' F F') : Prop :=
  p.h 0 = Filter.liminf p.h (nhds 0)

/-- (P*) is normal "in a dual manner" (p. 181): the minimization form (P′) of (P*), p. 173,
is normal, i.e. its perturbation function `p.dualH` on `E*` is lower semicontinuous at `0`. -/
def DualNormal (p : Program E E' F F') : Prop :=
  p.dualH 0 = Filter.liminf p.dualH (nhds 0)

end DualityStability.StrongDuality.Supplement


