-- Prove2me | Definitions.Def_PertComp_preDom
-- name    : PertComp_preDom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:19.303678+00:00
-- url     : https://prove2.me/theorems/16bdc8de-ec29-478f-872e-dcc623171cdb
-- title:
--   The set $f^{-1}(\operatorname{dom}\varphi)$ of Problem 1.1
-- statement:
--   For $\varphi\colon\mathbb R\to\,]-\infty,+\infty]$ and $f\colon X\to\,]-\infty,+\infty]$,
--   $$f^{-1}(\operatorname{dom}\varphi)=\{x\in X : f(x)\in\operatorname{dom}\varphi\},$$
--   the set that appears in conditions [b] and [d] of Problem 1.1.
--
--   **Formalization Note** $f(x)\in\operatorname{dom}\varphi$ means that $f(x)$ is a real number at which $\varphi$ is finite; for proper $f$ the real number is `(f x).toReal`.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Problem 1.1, p.2

import Mathlib

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, Problem 1.1 [b], [d], p.2: the set
`f⁻¹(dom φ) = {x | f(x) ∈ dom φ}`.

**Formalization Note.** `φ : ℝ → EReal`, `f : X → EReal`; `f(x) ∈ dom φ` means `f x` is a real
number (`≠ ⊤`) at which `φ` is finite. For proper `f` (never `⊥`, as in every statement of the
mission) `(f x).toReal` is `f(x)` whenever `f x ≠ ⊤`. -/
def preDom {X : Type*} (φ : ℝ → EReal) (f : X → EReal) : Set X :=
  {x | f x ≠ ⊤ ∧ φ (f x).toReal ≠ ⊤}

end PertComp


