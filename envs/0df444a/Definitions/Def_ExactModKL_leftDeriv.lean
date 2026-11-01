-- Prove2me | Definitions.Def_ExactModKL_leftDeriv
-- name    : ExactModKL_leftDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:04.197414+00:00
-- url     : https://prove2.me/theorems/e853b673-710d-4a8b-8358-6803c8f26f4d
-- title:
--   The left derivative $\varphi'_-(t)$
-- statement:
--   The left derivative of a function $\varphi$ at $t$ is
--   $$
--   \varphi'_-(t)=\lim_{s\to t^-}\frac{\varphi(s)-\varphi(t)}{s-t}.
--   $$
--   Concave functions on an interval have a left derivative at every interior point, even where they are not differentiable. The generalized concave KL property uses $\varphi'_-$ in place of $\varphi'$, which lets the desingularizing function have kinks.
--
--   **Formalization Note** The left derivative is the derivative of $\varphi$ at $t$ within the half-line $(-\infty,t)$ (`derivWithin φ (Set.Iio t) t`). It is not the two-sided derivative, which Lean sets to $0$ at a kink.
-- source:
--   Wang–Wang, arXiv:2008.13257v5, §3.1, p.8

import Mathlib

namespace ExactModKL

/-- The left derivative `ϕ′_−(t) = lim_{s→t−} (ϕ(s) − ϕ(t))/(s − t)` of `ϕ` at `t`
(Wang–Wang, arXiv:2008.13257v5 (preprint), §3.1, p.8).

**Formalization Note.** Written as `derivWithin ϕ (Set.Iio t) t`, the derivative of `ϕ` at `t`
within the open half-line `(−∞, t)`. It is not the two-sided `deriv ϕ t`, which is `0` at a
kink. For a concave function on `[0, η)` and `t ∈ (0, η)` the one-sided limit exists, so the
junk value `0` of `derivWithin` (no derivative) does not occur there. -/
noncomputable def leftDeriv (ϕ : ℝ → ℝ) (t : ℝ) : ℝ := derivWithin ϕ (Set.Iio t) t

end ExactModKL


