-- Prove2me | Definitions.Def_AnchoredEP_IsSubSolver
-- name    : AnchoredEP_IsSubSolver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:33.038555+00:00
-- url     : https://prove2.me/theorems/d6242356-a604-47c7-beb0-708a614893e6
-- title:
--   Exact solver for the regularized Taylor-model subproblem (87)
-- statement:
--   Let $F$ satisfy the hypotheses of the $p$th-order method with constant $L_p$, and let $H$ be set-valued. A map $\mathrm{sol}:\mathbb R\times\mathbb R^d\times\mathbb R^d\to\mathbb R^d$ is an **exact subproblem solver** if for every step $a>0$, every Taylor center $y$ and every point $w$, the point $z=\mathrm{sol}(a,y,w)$ satisfies
--   $$
--   0\in a\,\mathbb T^{(p-1)}_{L_p}(z;y)+aH(z)+z-w .
--   $$
--   In Algorithm 3 the center is $y=z_{k+\frac12}(a)$ and $w=\frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}z_k$; Eq. (87) states that this inclusion has a unique solution.
--
--   **Formalization Note** The theorems of the mission take the solver as a parameter and quantify over every map with this property.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 3, line 9, p.37, and Appendix G.2, Eq. (87), p.37

import Mathlib
import Definitions.Def_AnchoredEP_regTaylor

namespace AnchoredEP

/-- **An exact solver for the regularized Taylor-model subproblem (87).** Jiang–Yoon,
arXiv:2609.30212, Algorithm 3 line 9, p.37, and Appendix G.2, Eq. (87), p.37: for a trial step
`a > 0`, `z_{k+1}(a)` is "the unique solution of
`0 ∈ a P_{k,a}(z_{k+1}(a)) + a H(z_{k+1}(a)) + z_{k+1}(a) − (a/(A_k + a) z₀ + A_k/(A_k + a) z_k)`",
where `P_{k,a} = 𝕋_λ^{(p−1)}(·; z_{k+½}(a))` and `λ = L_p`.

`IsSubSolver F H p L sol` says that the map `sol : ℝ → ℝ^d → ℝ^d → ℝ^d` returns, for every step
`a > 0`, every Taylor center `y` and every point `w`, a point `z = sol a y w` with
`0 ∈ a 𝕋_L^{(p−1)}(z; y) + a H(z) + z − w`.

**Formalization Note.** The algorithm's subproblem oracle is a parameter `sol`; every theorem of
the mission quantifies over all maps satisfying this specification (by Eq. (87) there is
exactly one on `a > 0`). -/
def IsSubSolver {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d))) (p : ℕ) (L : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ a : ℝ, 0 < a → ∀ y w : EuclideanSpace ℝ (Fin d),
    ∃ h ∈ H (sol a y w), a • regTaylor F p L y (sol a y w) + a • h + sol a y w - w = 0

end AnchoredEP


