-- Prove2me | Definitions.Def_PADMPriv_IsProxMin
-- name    : PADMPriv_IsProxMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:02.670196+00:00
-- url     : https://prove2.me/theorems/00307959-0350-4c6a-9f9c-5c4560d73f77
-- title:
--   Minimizer of the extended proximal problem (13)
-- statement:
--   Let $F:\mathbb R^p\to\mathbb R$, $A\in\mathbb R^{m\times p}$, $\beta>0$ and $u\in\mathbb R^m$. A point $x\in\mathbb R^p$ is a minimizer of the **extended proximal problem** (13) if
--   $$
--   x \in P_{\beta,F,A}(u) := \operatorname*{arg\,min}_{x\in\mathbb R^p}\Big\{F(x)+\frac{\beta}{2}\|Ax-u\|_2^2\Big\}.
--   $$
--   Every update of PADM solves two such problems, one for the private loss and one for the public function $g$ (with $B$ in place of $A$).
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Eq. (13), p.7

import Mathlib

namespace PADMPriv

/-- `x` is a minimizer in the extended proximal problem (13) of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), p.7:
`x ∈ P_{β,F,A}(u) = argmin_{x ∈ ℝᵖ} {F(x) + (β/2)‖Ax − u‖₂²}`.

**Formalization Note** Vectors are `EuclideanSpace ℝ (Fin k)` and `A` acts through
`Matrix.toEuclideanLin`. -/
def IsProxMin {m p : ℕ} (β : ℝ) (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (u : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ x' : EuclideanSpace ℝ (Fin p),
    F x + β / 2 * ‖Matrix.toEuclideanLin A x - u‖ ^ 2 ≤
      F x' + β / 2 * ‖Matrix.toEuclideanLin A x' - u‖ ^ 2

end PADMPriv


