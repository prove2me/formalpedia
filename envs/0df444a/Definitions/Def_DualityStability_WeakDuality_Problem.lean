-- Prove2me | Definitions.Def_DualityStability_WeakDuality_Problem
-- name    : DualityStability_WeakDuality_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:37.371761+00:00
-- url     : https://prove2.me/theorems/95a7aa95-97a0-4796-94ba-5a1f3919e917
-- title:
--   The dual programs (P), (P*), the perturbation function inf (P(z)) and its l.s.c. hull, §§2–4
-- statement:
--   Let $(E,E^*)$ and $(F,F^*)$ be topologically paired real vector spaces, with pairings written $\langle\cdot,\cdot\rangle$. Let $A:E\to F$ be a continuous linear map and $A^*:F^*\to E^*$ a continuous linear map with
--   $$\langle Ax,y^*\rangle=\langle x,A^*y^*\rangle\qquad(x\in E,\ y^*\in F^*).$$
--   Let $f:E\to[-\infty,+\infty]$ be lower semicontinuous proper convex and $g:F\to[-\infty,+\infty]$ upper semicontinuous proper concave. Built from these data are:
--
--   1. the conjugates $f^*(x^*)=\sup_x\{\langle x,x^*\rangle-f(x)\}$ on $E^*$ and $g^*(y^*)=\inf_y\{\langle y,y^*\rangle-g(y)\}$ on $F^*$;
--   2. the dual problem (P\*), maximize $g^*(y^*)-f^*(A^*y^*)$ over $y^*\in F^*$, with value
--   $$\sup(\mathrm P^*)=\sup_{y^*\in F^*}\{g^*(y^*)-f^*(A^*y^*)\};$$
--   3. the perturbed primal problems (P($z$)), minimize $f(x)-g(Ax-z)$ over $x\in E$, for $z\in F$, and the perturbation function $h(z)=\inf(\mathrm P(z))=\inf_x\{f(x)-g(Ax-z)\}$, so that $h(0)=\inf(\mathrm P)$;
--   4. the lower semicontinuous hull of $h$, $\bar h(y)=\liminf_{z\to y}h(z)$, and its conjugate $\bar h^*(y^*)=\sup_y\{\langle y,y^*\rangle-\bar h(y)\}$.
--
--   Infima and suprema are taken in $[-\infty,+\infty]$. This is the standing setting of §3 of the paper, together with the perturbation of §4. Theorem 6 compares $\sup(\mathrm P^*)$ with $\bar h(0)$.
--
--   **Formalization Note** The data are bundled in a structure; $A^*$ is given as continuous linear data together with the adjoint identity. $f^*$ and $g^*$ are *defined* by the formulas (2.2) and (2.5), so "f and f\* conjugate to each other" is built in; the paper's facts that $f^*$ is l.s.c. proper convex and $g^*$ u.s.c. proper concave are consequences, not hypotheses. Upper semicontinuity of $g$ is Mathlib's `UpperSemicontinuous`. The lower limit is `Filter.liminf h (nhds y)` over the full neighbourhood filter of $y$, so $z=y$ is included and $\bar h\le h$. Subtraction is `EReal` subtraction; properness of $f$ and $g$ makes $f(x)-g(Ax-z)$ and $g^*(y^*)-f^*(A^*y^*)$ free of the undefined form $(+\infty)-(+\infty)$. The dual value is built from $f^*$, $g^*$ and $A^*$, never from $\bar h$.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), (2.1) and (2.2) p. 170, (2.5) p. 171, §3 pp. 171–172 (standing hypotheses, (P), (P*)), §4 p. 174 (P(z)), p. 180 (h̄, h̄*)

import Definitions.Def_DualityStability_WeakDuality_TopPairing
import Definitions.Def_DualityStability_WeakDuality_ConvexFunctions

namespace DualityStability.WeakDuality

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- The standing data of Rockafellar 1967, §3, pp. 171–172: paired spaces `(E, E*)` and
`(F, F*)`, a continuous linear `A : E → F` with continuous linear adjoint
`A* : F* → E*` (`⟨Ax, y*⟩ = ⟨x, A*y*⟩`), a lower semicontinuous proper convex
`f : E → [-∞, +∞]` and an upper semicontinuous proper concave `g : F → [-∞, +∞]`. -/
structure Problem (E E' F F' : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
    [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
    [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F']
    [LocallyConvexSpace ℝ F'] [T2Space F'] where
  pairE : TopPairing E E'
  pairF : TopPairing F F'
  A : E →L[ℝ] F
  Astar : F' →L[ℝ] E'
  adjoint : ∀ (x : E) (y' : F'), pairF.pair (A x) y' = pairE.pair x (Astar y')
  f : E → EReal
  g : F → EReal
  f_proper_convex : ProperConvex f
  f_lsc : LowerSemicontinuous f
  g_proper_concave : ProperConcave g
  g_usc : UpperSemicontinuous g

namespace Problem

variable (P : Problem E E' F F')

/-- The conjugate (2.2), p. 170: `f*(x*) = sup_x {⟨x, x*⟩ - f(x)}`. -/
noncomputable def fstar (x' : E') : EReal := ⨆ x : E, (P.pairE.pair x x' : EReal) - P.f x

/-- The concave conjugate (2.5), p. 171: `g*(y*) = inf_y {⟨y, y*⟩ - g(y)}`. -/
noncomputable def gstar (y' : F') : EReal := ⨅ y : F, (P.pairF.pair y y' : EReal) - P.g y

/-- The perturbation function of §4, p. 174: `h(z) = inf (P(z)) = inf_x {f(x) - g(Ax - z)}`. -/
noncomputable def perturbation (z : F) : EReal := ⨅ x : E, P.f x - P.g (P.A x - z)

/-- The l.s.c. hull (2.1), p. 170, of `h`: `h̄(y) = lim inf_{z → y} h(z)`, over the full
(unpunctured) neighbourhood filter of `y`. -/
noncomputable def hull (y : F) : EReal := Filter.liminf P.perturbation (nhds y)

/-- The conjugate (2.2) of `h̄` for the pairing `(F, F*)`: `h̄*(y*) = sup_y {⟨y, y*⟩ - h̄(y)}`. -/
noncomputable def hullConjugate (y' : F') : EReal :=
  ⨆ y : F, (P.pairF.pair y y' : EReal) - P.hull y

/-- The maximand of (P*), p. 172: `g*(y*) - f*(A*y*)`. -/
noncomputable def dualMaximand (y' : F') : EReal := P.gstar y' - P.fstar (P.Astar y')

/-- `sup (P*) = sup_{y*} {g*(y*) - f*(A*y*)}`, p. 172. -/
noncomputable def dualSup : EReal := ⨆ y' : F', P.dualMaximand y'

end Problem
end DualityStability.WeakDuality


