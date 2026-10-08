-- Prove2me | Definitions.Def_SelfScaledIPM_FuncProx_Directions
-- name    : SelfScaledIPM_FuncProx_Directions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:53.438195+00:00
-- url     : https://prove2.me/theorems/7ab072aa-bf9e-4146-9c89-2eef766a2e13
-- title:
--   Definitions 5.1, 5.5, (5.25)–(5.26) and §7 — affine-scaling and centering directions, Newton step and run, neighbourhood F(β)
-- statement:
--   Fix problem data $A:E\to Y$, $b$, $c$ as in the setting file, a strictly feasible $(x,y,s)$, and the scaling point $w$ of $(x,s)$, i.e. $F''(w)x=s$.
--
--   1. The **affine-scaling direction** (Definition 5.1) is the solution $(p_x,p_y,p_s)$ of
--   $$F''(w)p_x+p_s=s,\qquad Ap_x=0,\qquad A^*p_y+p_s=0. \tag{5.1}$$
--   2. The **centering direction** (Definition 5.5) is the solution $(d_x,d_y,d_s)$ of
--   $$F''(w)d_x+d_s=s+\mu(x,s)F'(x),\qquad Ad_x=0,\qquad A^*d_y+d_s=0. \tag{5.17}$$
--   3. A **Newton step** (5.25)–(5.26) maps $(x,y,s)$ to $(x-\alpha d_x,\ y-\alpha d_y,\ s-\alpha d_s)$, where
--   $$\alpha=\frac{1}{1+\gamma_\infty(x,s)+\bar\sigma},\qquad \bar\sigma=\max\{\sigma_x(d_x),\sigma_s(d_s)\}.$$
--   A **Newton run** is a sequence $(z_j)_{j\ge0}$ of triples in which each $z_{j+1}$ is obtained from $z_j$ by a Newton step.
--   4. The **functional-proximity neighbourhood** (§7) is $\mathcal F(\beta)=\{(x,y,s)\ \text{strictly feasible}:\gamma_F(x,s)\le\beta\}$.
--
--   These are the two search directions of the primal-dual methods and the corrector process and neighbourhood of the predictor-corrector Algorithm 7.1.
--
--   **Formalization Note** Directions and steps are predicates on their defining linear systems, never computed by inverting a matrix; the scaling point and the direction are existentially quantified inside the Newton step. The affine-scaling system does not mention $x$ itself (only through $s=F''(w)x$), so `IsAffineScalingDir` takes $s$ and $w$. Triples are elements of $E\times Y\times E$. A Newton step does not itself assert that its starting point is strictly feasible; every statement that uses it says so where needed.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 21 Definition 5.1 (5.1); p. 24 Definition 5.5 (5.17); p. 25 (5.25)–(5.26); p. 31 F(β)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Affine-scaling direction** (Definition 5.1, (5.1), p. 21): `(p_x, p_y, p_s)` solves
`F''(w)p_x + p_s = s`, `A p_x = 0`, `A* p_y + p_s = 0`, where `w` is the scaling point of `(x, s)`
(`F''(w)x = s`; `x` itself does not enter the system). -/
def IsAffineScalingDir {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (s w : EuclideanSpace ℝ (Fin n))
    (px : EuclideanSpace ℝ (Fin n)) (py : EuclideanSpace ℝ (Fin m))
    (ps : EuclideanSpace ℝ (Fin n)) : Prop :=
  SelfScaledIPM.ShortStep.hess F w px + ps = s ∧ A px = 0 ∧ ContinuousLinearMap.adjoint A py + ps = 0

/-- **Centering direction** (Definition 5.5, (5.17), p. 24): `(d_x, d_y, d_s)` solves
`F''(w)d_x + d_s = s + µ(x, s)F'(x)`, `A d_x = 0`, `A* d_y + d_s = 0`. -/
def IsCenteringDir {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (x s w : EuclideanSpace ℝ (Fin n))
    (dx : EuclideanSpace ℝ (Fin n)) (dy : EuclideanSpace ℝ (Fin m))
    (ds : EuclideanSpace ℝ (Fin n)) : Prop :=
  SelfScaledIPM.ShortStep.hess F w dx + ds = s + SelfScaledIPM.ShortStep.mu ν x s • gradient F x ∧ A dx = 0 ∧
    ContinuousLinearMap.adjoint A dy + ds = 0

/-- **One step of the Newton process** (5.25)–(5.26), p. 25: from `(x, y, s)` to
`(x − α d_x, y − α d_y, s − α d_s)`, where `w` is the scaling point of `(x, s)`, `(d_x, d_y, d_s)`
the centering direction, `σ̄ = max {σ_x(d_x), σ_s(d_s)}` (`d_x ∈ E` at `x ∈ int K`, `d_s ∈ E*` at
`s ∈ int K*`) and `α = 1/(1 + γ_∞(x, s) + σ̄)`. Points are triples `(x, y, s) ∈ E × Y × E`. -/
def IsNewtonStep {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (z z' : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∃ (w dx : EuclideanSpace ℝ (Fin n)) (dy : EuclideanSpace ℝ (Fin m))
    (ds : EuclideanSpace ℝ (Fin n)),
    SelfScaledIPM.ShortStep.IsScalingPoint K F z.1 z.2.2 w ∧ IsCenteringDir A F ν z.1 z.2.2 w dx dy ds ∧
    z' = (z.1 - (1 / (1 + gammaInf K F ν z.1 z.2.2 +
              max (SelfScaledIPM.ShortStep.sigma K z.1 dx) (SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) z.2.2 ds))) • dx,
          z.2.1 - (1 / (1 + gammaInf K F ν z.1 z.2.2 +
              max (SelfScaledIPM.ShortStep.sigma K z.1 dx) (SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) z.2.2 ds))) • dy,
          z.2.2 - (1 / (1 + gammaInf K F ν z.1 z.2.2 +
              max (SelfScaledIPM.ShortStep.sigma K z.1 dx) (SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) z.2.2 ds))) • ds)

/-- **Run of the Newton process** (5.25): `z (j + 1)` is obtained from `z j` by one Newton step,
for every `j`. -/
def IsNewtonRun {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (z : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∀ j, IsNewtonStep K F ν A (z j) (z (j + 1))

/-- **Functional-proximity neighbourhood** `F(β)` (§7, p. 31): the strictly feasible triples
`(x, y, s)` with `γ_F(x, s) ≤ β`. -/
def InFuncNbhd {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsStrictlyFeasible K A b c z.1 z.2.1 z.2.2 ∧ gammaF K F ν z.1 z.2.2 ≤ β

end SelfScaledIPM.FuncProx


