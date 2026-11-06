-- Prove2me | Definitions.Def_AnchoredEP_LineSearchReturnsWithin
-- name    : AnchoredEP_LineSearchReturnsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:32.309723+00:00
-- url     : https://prove2.me/theorems/df792968-0d7c-4a78-9b5d-944fe833cccd
-- title:
--   The line search returns within $n$ trial evaluations
-- statement:
--   The line search at outer iteration $k$ first evaluates the upper trial $\bar a_k$ and stops if it passes; otherwise it bisects until a midpoint is accepted. Counting the initial capped trial and the final successful bisection trial, a search whose $t$-th bisection trial ($t=0,1,\dots$) is the first accepted one uses $t+2$ trial evaluations.
--
--   The search **returns within $n$ trial evaluations** if the upper trial passes and $n\ge1$, or some bisection trial $t$ with $t+2\le n$ is accepted. In particular the predicate asserts that the search returns: it fails for every $n$ when the upper trial fails and no bisection trial is ever accepted.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2–G.3, pp.38–40

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_accepted
import Definitions.Def_AnchoredEP_upperPasses

namespace AnchoredEP

/-- **The line search returns within `n` trial evaluations.** Jiang–Yoon, arXiv:2609.30212,
Appendix G.2–G.3, pp.38–40: the line search first evaluates the upper trial `ā_k`; if
`ψ_k(ā_k) ≤ p!ρ` it stops after this one trial, otherwise it runs the bisection (91) until a
midpoint is accepted. "Including the initial capped trial and the final successful bisection
trial" (p.40), a search whose `t`-th bisection trial (`t = 0, 1, …`) is accepted uses `t + 2`
trial evaluations.

`LineSearchReturnsWithin F p L ε sol z0 s n` holds when the upper trial terminates and `1 ≤ n`,
or some bisection trial `t` with `t + 2 ≤ n` is accepted. It asserts that the search returns:
it is false for a state whose upper trial fails and whose bisection never accepts.

**Formalization Note.** After the first acceptance the interval is frozen (`bisect`), so an
accepted `t` with `t + 2 ≤ n` exists iff the first accepted trial has index at most `n − 2`. -/
def LineSearchReturnsWithin {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (n : ℕ) : Prop :=
  (upperPasses F p L ε sol z0 s ∧ 1 ≤ n) ∨
    ∃ t : ℕ, accepted F p L ε sol z0 s t ∧ t + 2 ≤ n

end AnchoredEP


