-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonBisect
-- name    : AnchoredEP_Supplement_newtonBisect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:05:51.783787+00:00
-- url     : https://prove2.me/theorems/7544a841-a047-4025-a547-f137a9e8a779
-- title:
--   Bisection intervals of Subroutine 1
-- statement:
--   Subroutine 1 of the AEP Newton method, when the upper trial fails, starts from the interval $[a^-,a^+]=[0,\bar a_k]$ and repeatedly evaluates the midpoint $a=(a^-+a^+)/2$:
--
--   1. if $\varphi_k(a)<1$, the lower endpoint is replaced by $a$;
--   2. if $\varphi_k(a)>\sqrt2$, the upper endpoint is replaced by $a$;
--   3. otherwise the trial is accepted.
--
--   This definition gives the interval $(a^-,a^+)$ before the $t$-th bisection trial, $t=0,1,\dots$; the $t$-th trial is evaluated at its midpoint.
--
--   **Formalization Note** After a midpoint is accepted the interval is kept fixed, so all later midpoints equal the accepted step; the step chosen by the line search is the midpoint at the first accepted index.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Subroutine 1, p.25; Section 4.1, p.9

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_Supplement_newtonPhi
import Definitions.Def_AnchoredEP_Supplement_newtonAbar

namespace AnchoredEP.Supplement

/-- **The bisection intervals of Subroutine 1.** Jiang–Yoon, arXiv:2609.30212, Subroutine 1, p.25
(and Section 4.1, p.9): starting from `a⁻ = 0`, `a⁺ = ā_k`, each step evaluates
`a = (a⁻ + a⁺)/2`; "if `φ_k(a) < 1` then set `a⁻ = a`; else if `φ_k(a) > √2` then set `a⁺ = a`;
else accept `a_k = a`".

`newtonBisect F L ε sol z0 s t = (a⁻, a⁺)` is the interval before the `t`-th bisection trial
(`t = 0, 1, …`); the `t`-th trial is evaluated at its midpoint.

**Formalization Note.** Once a midpoint is accepted the interval is frozen, so every later
midpoint is the accepted step; the line search's step is the midpoint at the first accepted `t`
(`newtonAccepted`, `newtonStepSize`). -/
noncomputable def newtonBisect {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) : ℕ → ℝ × ℝ
  | 0 => (0, newtonAbar F L ε s)
  | t + 1 =>
    let I := newtonBisect F L ε sol z0 s t
    let m := (I.1 + I.2) / 2
    if newtonPhi F L sol z0 s m < 1 then (m, I.2)
    else if Real.sqrt 2 < newtonPhi F L sol z0 s m then (I.1, m)
    else I

end AnchoredEP.Supplement


