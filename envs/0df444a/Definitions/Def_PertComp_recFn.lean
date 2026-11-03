-- Prove2me | Definitions.Def_PertComp_recFn
-- name    : PertComp_recFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:18.880907+00:00
-- url     : https://prove2.me/theorems/d5673464-12be-404c-94e1-71fcdff7a202
-- title:
--   Recession function $\operatorname{rec} f$
-- statement:
--   The **recession function** of $f$ is
--   $$(\operatorname{rec} f)(y)=\sup_{x\in\operatorname{dom} f}\big(f(x+y)-f(x)\big).$$
--   It is the value of the perspective (2.7) at $\xi=0$.
--
--   **Formalization Note** Computed in `EReal` for every $f$; the paper uses it for proper $f$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, §2, p.5

import Mathlib

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, §2, p.5: the *recession function*
`(rec f)(y) = sup_{x ∈ dom f} (f(x + y) − f(x))`.

**Formalization Note.** Computed in `EReal`, for every `f`; the paper uses it for proper `f`. -/
noncomputable def recFn {V : Type*} [AddCommGroup V] (f : V → EReal) (y : V) : EReal :=
  ⨆ (x : V) (_ : f x ≠ ⊤), f (x + y) - f x

end PertComp


