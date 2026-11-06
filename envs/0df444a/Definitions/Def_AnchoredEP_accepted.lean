-- Prove2me | Definitions.Def_AnchoredEP_accepted
-- name    : AnchoredEP_accepted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:41:29.849305+00:00
-- url     : https://prove2.me/theorems/cd3fcd56-9b5a-4c3a-a1f9-13ed26f5f5a8
-- title:
--   Acceptance of a bisection trial
-- statement:
--   The $t$-th bisection trial is **accepted** if the midpoint $a$ of the $t$-th interval satisfies
--   $$
--   \frac{p!\rho}{\sqrt2}\le\psi_k(a)\le p!\rho,\qquad \rho=\frac1{\sqrt2},
--   $$
--   which is the acceptance window (84).
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (91), p.38, and Eq. (84), p.36

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_psi
import Definitions.Def_AnchoredEP_bisect

namespace AnchoredEP

/-- **Acceptance of the `t`-th bisection trial.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2,
Eq. (91), p.38: the trial `a = (a⁻ + a⁺)/2` is accepted when `p!ρ/√2 ≤ ψ_k(a) ≤ p!ρ`, with
`ρ = 1/√2` (equivalently the window (84), p.36).

`accepted F p L ε sol z0 s t` says that the midpoint of `bisect … s t` lies in this window. -/
def accepted {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (t : ℕ) : Prop :=
  (p.factorial : ℝ) * (1 / Real.sqrt 2) / Real.sqrt 2 ≤
      psi F p L sol z0 s (((bisect F p L ε sol z0 s t).1 + (bisect F p L ε sol z0 s t).2) / 2) ∧
    psi F p L sol z0 s (((bisect F p L ε sol z0 s t).1 + (bisect F p L ε sol z0 s t).2) / 2) ≤
      (p.factorial : ℝ) * (1 / Real.sqrt 2)

end AnchoredEP


