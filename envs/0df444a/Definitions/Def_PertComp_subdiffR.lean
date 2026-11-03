-- Prove2me | Definitions.Def_PertComp_subdiffR
-- name    : PertComp_subdiffR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:16.809822+00:00
-- url     : https://prove2.me/theorems/2d591616-890c-4d45-8cc5-1d6c7ffe15db
-- title:
--   Subdifferential of a function on $\mathbb R$
-- statement:
--   For $\varphi\colon\mathbb R\to[-\infty,+\infty]$ and $t\in\mathbb R$, the subdifferential (2.6) is
--   $$\partial\varphi(t)=\{s\in\mathbb R : (u-t)s+\varphi(t)\le\varphi(u)\ \text{for all } u\},$$
--   with $\mathbb R^*$ identified with $\mathbb R$. It is used for $\partial\varphi(f(x))$ in (2.15) and for $\partial\varphi^*(\xi^*)$ in (3.3) and (3.12).
--
--   **Formalization Note** The inequality is required for every $u$ rather than every $u\in\operatorname{dom}\varphi$; the two agree because it holds trivially when $\varphi(u)=+\infty$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (2.6), p.5, on ℝ

import Mathlib

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (2.6), p.5, on the real line: the
subdifferential of `φ : ℝ → [−∞, +∞]` at `t` is the set of `s ∈ ℝ` with
`(u − t) s + φ(t) ≤ φ(u)` for every `u` (equivalently every `u ∈ dom φ`).

**Formalization Note.** `ℝ*` (and `ℝ**`) are identified with `ℝ`; the inequality is in `EReal`.
Imposing it for all `u` rather than `u ∈ dom φ` changes nothing, since it holds trivially when
`φ(u) = +∞`. -/
def subdiffR (φ : ℝ → EReal) (t : ℝ) : Set ℝ :=
  {s | ∀ u : ℝ, φ t + ((s * (u - t) : ℝ) : EReal) ≤ φ u}

end PertComp


