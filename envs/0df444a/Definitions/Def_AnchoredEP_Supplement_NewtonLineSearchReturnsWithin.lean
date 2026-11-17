-- Prove2me | Definitions.Def_AnchoredEP_Supplement_NewtonLineSearchReturnsWithin
-- name    : AnchoredEP_Supplement_NewtonLineSearchReturnsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:09:06.534638+00:00
-- url     : https://prove2.me/theorems/8cb58a00-2534-4903-b639-7b1b49c603cd
-- title:
--   Subroutine 1 returns within $n$ trial evaluations
-- statement:
--   A **trial evaluation** of Subroutine 1 computes $z_{k+\frac12}(a)$, $z_{k+1}(a)$ and $v_{k+1}(a)$ for one value $a$. Subroutine 1 first evaluates the trial at $\bar a_k$; if $\varphi_k(\bar a_k)\le\sqrt2$ it stops after this single evaluation, and otherwise it bisects until a midpoint is accepted. Counting the initial trial at $\bar a_k$, a search whose first accepted bisection trial has index $t$ ($t=0,1,\dots$) uses $t+2$ trial evaluations.
--
--   The predicate *Subroutine 1 returns within $n$ trial evaluations* holds when either the upper trial passes and $n\ge1$, or some bisection trial $t$ with $t+2\le n$ is accepted. In particular it asserts that the line search terminates.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Subroutine 1, p.25; Section 4.2 and Theorem 4.6, p.10

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_Supplement_newtonAccepted
import Definitions.Def_AnchoredEP_Supplement_newtonUpperPasses

namespace AnchoredEP.Supplement

/-- **Subroutine 1 returns within `n` trial evaluations.** Jiang–Yoon, arXiv:2609.30212,
Subroutine 1, p.25, and Section 4.2, p.10: a trial evaluation computes `z_{k+½}(a)`, `z_{k+1}(a)`
and `v_{k+1}(a)` for one `a`. Subroutine 1 first evaluates the trial at `ā_k`; if
`φ_k(ā_k) ≤ √2` it returns after this one trial, otherwise it runs the bisection until a midpoint
is accepted. Including the initial trial at `a = ā_k` (Theorem 4.6, p.10), a search whose `t`-th
bisection trial (`t = 0, 1, …`) is the first accepted one uses `t + 2` trial evaluations.

`NewtonLineSearchReturnsWithin F L ε sol z0 s n` holds when the upper trial terminates and
`1 ≤ n`, or some bisection trial `t` with `t + 2 ≤ n` is accepted. It asserts that the search
returns: it is false for a state whose upper trial fails and whose bisection never accepts.

**Formalization Note.** After the first acceptance the interval is frozen (`newtonBisect`), so an
accepted `t` with `t + 2 ≤ n` exists iff the first accepted trial has index at most `n − 2`. -/
def NewtonLineSearchReturnsWithin {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (n : ℕ) : Prop :=
  (newtonUpperPasses F L ε sol z0 s ∧ 1 ≤ n) ∨
    ∃ t : ℕ, newtonAccepted F L ε sol z0 s t ∧ t + 2 ≤ n

end AnchoredEP.Supplement


