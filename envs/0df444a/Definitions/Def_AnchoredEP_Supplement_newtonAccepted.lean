-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonAccepted
-- name    : AnchoredEP_Supplement_newtonAccepted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:06:55.859461+00:00
-- url     : https://prove2.me/theorems/3edae0ae-5e8e-4ba3-8d44-79f51c4e179f
-- title:
--   Acceptance of a bisection trial in Subroutine 1
-- statement:
--   The $t$-th bisection trial of Subroutine 1 (the midpoint $a$ of the $t$-th interval) is **accepted** when
--   $$
--   1\le\varphi_k(a)\le\sqrt2,
--   $$
--   the acceptance window (23). An accepted trial satisfies the AEP relative-error condition with $\rho=1/\sqrt2$ and the step-size lower bound (20).
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Eq. (23), p.9; Subroutine 1 lines 11–16, p.25

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_Supplement_newtonPhi
import Definitions.Def_AnchoredEP_Supplement_newtonBisect

namespace AnchoredEP.Supplement

/-- **Acceptance of the `t`-th bisection trial of Subroutine 1.** Jiang–Yoon, arXiv:2609.30212,
Eq. (23), p.9, and Subroutine 1 lines 11–16, p.25: the trial `a = (a⁻ + a⁺)/2` is accepted when
`1 ≤ φ_k(a) ≤ √2`.

`newtonAccepted F L ε sol z0 s t` says that the midpoint of `newtonBisect … s t` lies in this
window. -/
def newtonAccepted {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (t : ℕ) : Prop :=
  1 ≤ newtonPhi F L sol z0 s
      (((newtonBisect F L ε sol z0 s t).1 + (newtonBisect F L ε sol z0 s t).2) / 2) ∧
    newtonPhi F L sol z0 s
      (((newtonBisect F L ε sol z0 s t).1 + (newtonBisect F L ε sol z0 s t).2) / 2) ≤ Real.sqrt 2

end AnchoredEP.Supplement


