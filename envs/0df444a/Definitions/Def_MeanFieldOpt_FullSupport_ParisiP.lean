-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_ParisiP
-- name    : MeanFieldOpt_FullSupport_ParisiP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:47:10.841776+00:00
-- url     : https://prove2.me/theorems/08032db2-0a09-4c1b-b7ee-610356e0956e
-- title:
--   The extended Parisi functional $\mathsf P(\gamma)$ (Eq. (1.6))
-- statement:
--   Let $\xi$ be a mixture, $f_0$ a terminal condition and $\gamma \in \mathscr L$. The **Parisi functional** is
--
--   $$
--   \mathsf P(\gamma) = \Phi^\gamma(0,0) - \frac12 \int_0^1 t\,\xi''(t)\,\gamma(t)\,dt,
--   $$
--
--   where $\Phi^\gamma$ is the solution of the Parisi PDE with terminal condition $\Phi(1,x) = f_0(x)$, defined by continuity from step functions. For $f_0(x) = |x|$ this is the zero-temperature Parisi functional of Eqs. (1.5)–(1.6); the extended variational principle minimizes it over $\mathscr L$.
--
--   **Formalization Note** The functional is parametrized by $f_0$; Section 6.1 of the paper works with a general admissible $f_0$, and Theorem 5 specializes to $f_0 = |\cdot|$. The integral is over $[0,1)$, which has the same value as over $[0,1]$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 3, Eq. (1.6); extended to ℒ on p. 7 and p. 24

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_PhiL

open MeasureTheory

namespace MeanFieldOpt.FullSupport

/-- The (extended) Parisi functional (arXiv:2001.00904v1, p. 3, Eq. (1.6)):
`P(γ) = Φ^γ(0, 0) - (1/2) ∫_0^1 t ξ''(t) γ(t) dt`, with `Φ^γ` solving (6.2) with terminal
condition `f₀` (for `f₀ = |·|` this is (1.5)–(1.6)). -/
noncomputable def ParisiP (ξ : Mixture) (f₀ : ℝ → ℝ) (γ : ℝ → ℝ) : ℝ :=
  PhiL ξ f₀ γ 0 0 - (1 / 2) * ∫ t in Set.Ico (0 : ℝ) 1, t * ξ.d2 t * γ t

end MeanFieldOpt.FullSupport


