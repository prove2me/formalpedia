-- Prove2me | Definitions.Def_AnchoredEP_Supplement_IsNewtonSolver
-- name    : AnchoredEP_Supplement_IsNewtonSolver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:04:01.732508+00:00
-- url     : https://prove2.me/theorems/bd6d2c7a-9464-41b3-a314-9d56f2397c5d
-- title:
--   Exact solver for the affine-model subproblem (17) of AEP Newton
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$ be differentiable and $H:\mathbb R^d\rightrightarrows\mathbb R^d$ set-valued. At an outer iteration of the Anchored Extra-Proximal (AEP) Newton method, a trial step $a>0$ requires the solution $z$ of the inclusion
--   $$
--   0\in a\big(F(y)+DF(y)(z-y)\big)+aH(z)+z-w,
--   $$
--   where $y=z_{k+\frac12}(a)$ is the point at which the Jacobian is evaluated and $w=\frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}z_k$ is the anchored point. The affine map $z\mapsto F(y)+DF(y)(z-y)$ is the first-order Taylor model of $F$ at $y$.
--
--   A map $\mathrm{sol}:\mathbb R\times\mathbb R^d\times\mathbb R^d\to\mathbb R^d$ is an **exact solver** of these subproblems if, for every $a>0$ and all $y,w$, the point $z=\mathrm{sol}(a,y,w)$ satisfies the inclusion above, i.e. some $h\in H(z)$ has $a(F(y)+DF(y)(z-y))+ah+z-w=0$.
--
--   When $F$ is monotone and $H$ maximal monotone the subproblem has exactly one solution (Minty's theorem), so all exact solvers agree on $a>0$; the theorems about the method quantify over every exact solver.
--
--   **Formalization Note** The Taylor model is the published `taylorOp F 2 y z`.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Eq. (17), p.7; Algorithm 1 line 9, p.8; Eq. (49), p.25

import Mathlib
import Definitions.Def_AnchoredEP_taylorOp

namespace AnchoredEP.Supplement

/-- **An exact solver for the affine-model subproblem (17)/(49) of AEP Newton.** Jiang–Yoon,
*Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems*,
arXiv:2609.30212, Eq. (17), p.7, Algorithm 1 line 9, p.8, and Eq. (49), p.25: for a trial step
`a > 0`, `z_{k+1}(a)` solves
`0 ∈ a P_{k,a}(z_{k+1}(a)) + a H(z_{k+1}(a)) + z_{k+1}(a) − (a/(A_k + a) z₀ + A_k/(A_k + a) z_k)`,
where `P_{k,a}(z) = F(z_{k+½}(a)) + DF(z_{k+½}(a))(z − z_{k+½}(a))` is the affine Taylor model.

`IsNewtonSolver F H sol` says that for every step `a > 0`, every Taylor center `y` and every
anchored point `w`, the point `z = sol a y w` satisfies
`0 ∈ a (F(y) + DF(y)(z − y)) + a H(z) + z − w`.

**Formalization Note.** The affine model is the published `taylorOp F 2 y z`
(`= F y + iteratedFDeriv ℝ 1 F y (fun _ => z - y) = F(y) + DF(y)(z − y)`). The subproblem oracle
is a parameter; the theorems quantify over every map meeting this specification (p.7: the
solution is unique by Minty's theorem, so every such map gives the source's iterates). -/
def IsNewtonSolver {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ y w : EuclideanSpace ℝ (Fin d),
    ∃ h ∈ H (sol a y w), a • taylorOp F 2 y (sol a y w) + a • h + sol a y w - w = 0

end AnchoredEP.Supplement


