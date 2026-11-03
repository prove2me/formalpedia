-- Prove2me | Definitions.Def_DCAExtrap_IsCriticalPoint
-- name    : DCAExtrap_IsCriticalPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:13.606595+00:00
-- url     : https://prove2.me/theorems/830fd14e-3f3e-4bd8-99a5-80a707ad95b9
-- title:
--   Critical point of problem (1)
-- statement:
--   A point $x^*\in E$ is a **critical point** of problem (1) if
--
--   $$
--   \bigl[\nabla f(x^*) + \partial g(x^*)\bigr]\cap \partial h(x^*) \neq \emptyset,
--   $$
--
--   that is, some $\xi\in\partial h(x^*)$ satisfies $\xi-\nabla f(x^*)\in\partial g(x^*)$. Here $\partial g$ and $\partial h$ are convex subdifferentials. In particular $g(x^*)<+\infty$.
--
--   Theorems 3.1(c) and 3.2 conclude that limit points, respectively limits, of DCAe sequences are critical points.
--
--   **Formalization Note** The page prints the condition with an unclosed bracket, $[\nabla f(x^*)+\partial g(x^*)\cap\partial h(x^*)\neq\emptyset$; the bracket is closed after $\partial g(x^*)$, which is the set that (23) on p.8 shows to be nonempty.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, §2, p.4, critical point of (1); cf. (23), p.8

import Mathlib
import Definitions.Def_DCAExtrap_convexSubdiff

namespace DCAExtrap

/-- **Critical point of problem (1)** (Phan–Le Thi, arXiv:2106.04743v1, §2, p.4): `x*` is a
critical point of (1) iff `[∇f(x*) + ∂g(x*)] ∩ ∂h(x*) ≠ ∅`, i.e. some `ξ ∈ ∂h(x*)` satisfies
`ξ − ∇f(x*) ∈ ∂g(x*)`.

**Formalization Note.** The page prints `[∇f(x*) + ∂g(x*) ∩ ∂h(x*) ≠ ∅` with an unclosed
bracket; the reading `[∇f(x*) + ∂g(x*)] ∩ ∂h(x*) ≠ ∅` is the one the proof of Theorem 3.1(c)
establishes ((23), p.8). `∂g` and `∂h` are subdifferentials of convex analysis (`convexSubdiff`);
`∂g(x*) ≠ ∅` forces `g(x*) < +∞`. -/
noncomputable def IsCriticalPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (g : E → EReal) (h : E → ℝ) (x : E) : Prop :=
  ∃ ξ ∈ convexSubdiff (fun y => ((h y : ℝ) : EReal)) x, ξ - gradient f x ∈ convexSubdiff g x

end DCAExtrap


