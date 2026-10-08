-- Prove2me | Definitions.Def_QueueingFundamentals_Transient_laplace
-- name    : QueueingFundamentals_Transient_laplace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:32:14.70002+00:00
-- url     : https://prove2.me/theorems/9dabe191-82ad-4be7-bfd5-15554a4727c4
-- title:
--   Laplace transform of a function on $[0,\infty)$
-- statement:
--   For a real function $f$ on $[0,\infty)$ and a complex number $s$, the **Laplace transform** of $f$ at $s$ is
--
--   $$
--   \bar f(s) = \int_0^\infty e^{-st} f(t)\,dt .
--   $$
--
--   In §2.11.2 the book uses it for $\operatorname{Re} s > 0$, where it converges for every bounded measurable $f$; this is how the transforms $\bar p_0(s)$ of the M/M/1 queue and of its busy period are defined.
--
--   **Formalization Note** The integral is a Bochner integral over $(0,\infty)$ of the complex-valued function $t \mapsto e^{-st} f(t)$. It returns $0$ when the integrand is not integrable, so every statement that uses it also asserts the integrability.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.99, definition of the Laplace transform P̄(z, s), §2.11.2

import Mathlib

namespace QueueingFundamentals.Transient

open MeasureTheory

/-- The Laplace transform `f̄(s) = ∫_0^∞ e^{-st} f(t) dt` of a real function `f` on `[0, ∞)`, at a
complex argument `s` (p.99). It is a Bochner integral over `(0, ∞)`; statements that use it state
the integrability they need. -/
noncomputable def laplace (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-s * (t : ℂ)) * (f t : ℂ)

end QueueingFundamentals.Transient


