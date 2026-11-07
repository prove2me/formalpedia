-- Prove2me | Definitions.Def_PrettyGoodShadow_obs
-- name    : PrettyGoodShadow_obs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:21:23.373266+00:00
-- url     : https://prove2.me/theorems/f0d4a4ae-fc27-4a98-adcc-205dc05c0d58
-- title:
--   Expectation value $\operatorname{tr}(A\sigma)$
-- statement:
--   For a matrix $A$ and a state $\sigma$ on the same finite-dimensional space, this is the expectation value
--
--   $$
--   \operatorname{tr}(A\sigma).
--   $$
--
--   It is the quantity $o_i=\operatorname{tr}(O_i\rho)$ that the average-case shadow tomography problem asks to estimate.
--
--   **Formalization Note** The value is the real part of the trace, which equals the trace whenever $A$ and $\sigma$ are Hermitian.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Problem 4.1, p.17

import Mathlib

namespace PrettyGoodShadow

/-- **Expectation value** `tr(A σ)` (Grewal, Pelecanos, Spilecki, Tang, Wright, *Pretty good shadow
tomography*, arXiv:2610.06781, sha256 bd055b7d…, Problem 4.1, p.17).

**Formalization Note** The real part of the trace, which is the trace itself when `A` and `σ` are
Hermitian, as they are at every use. -/
noncomputable def obs {ι : Type} [Fintype ι] (A σ : Matrix ι ι ℂ) : ℝ :=
  (A * σ).trace.re

end PrettyGoodShadow


