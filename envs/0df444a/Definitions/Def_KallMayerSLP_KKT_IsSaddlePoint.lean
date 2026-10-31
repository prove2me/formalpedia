-- Prove2me | Definitions.Def_KallMayerSLP_KKT_IsSaddlePoint
-- name    : KallMayerSLP_KKT_IsSaddlePoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:33.988995+00:00
-- url     : https://prove2.me/theorems/4a325c9e-a3f4-441f-9db4-2a838f71e5d0
-- title:
--   Saddle point of the Lagrange function (3.6)
-- statement:
--   A pair $(\hat x,\hat u)$ with $\hat u\ge 0$ is a **saddle point** of the Lagrange function $L$ of (3.1) if
--   $$
--   L(\hat x,u)\le L(\hat x,\hat u)\le L(x,\hat u)\qquad\forall u\ge 0,\ \forall x\in\mathbb R^n. \tag{3.6}
--   $$
--
--   Every KKT point is a saddle point (p.66), and a saddle point solves both problems in (3.7) (Proposition 3.5).
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, eq. (3.6), p.66 (PDF 77)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_lagrangian

namespace KallMayerSLP.KKT

/-- **Saddle point `(x̂, û ≥ 0)` of the Lagrange function (3.6).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, eq. (3.6), p.66 (PDF 77):
"`L(x̂, u) ≤ L(x̂, û) ≤ L(x, û) ∀u ≥ 0, ∀x ∈ ℝⁿ`", for a pair with `û ≥ 0`.

**Formalization Note.** `û ≥ 0` and `u ≥ 0` are the componentwise order on `Fin m → ℝ`. -/
def IsSaddlePoint {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (xh : EuclideanSpace ℝ (Fin n))
    (uh : Fin m → ℝ) : Prop :=
  0 ≤ uh ∧
  (∀ u : Fin m → ℝ, 0 ≤ u → lagrangian f g xh u ≤ lagrangian f g xh uh) ∧
  ∀ x, lagrangian f g xh uh ≤ lagrangian f g x uh

end KallMayerSLP.KKT


