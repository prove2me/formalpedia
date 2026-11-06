-- Prove2me | Definitions.Def_RollingProbeQN_Convex_bisectPass
-- name    : RollingProbeQN_Convex_bisectPass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:04.459088+00:00
-- url     : https://prove2.me/theorems/c6cd1662-ea66-48ec-8970-5ea310404dfd
-- title:
--   One pass of the bisection loop of Subroutine 1.1
-- statement:
--   One pass of Step 3 of Subroutine 1.1 on a bracket $(\lambda^-,\lambda^+)$ and a counter $n$: if $\lambda^+/\lambda^->2^{1/4}$, set $\lambda=\sqrt{\lambda^-\lambda^+}$, evaluate $\Psi(\lambda)$, and replace $\lambda^-$ by $\lambda$ if $\Psi(\lambda)<\sigma$ and $\lambda^+$ by $\lambda$ otherwise, adding one to $n$; if $\lambda^+/\lambda^-\le2^{1/4}$, do nothing.
--
--   **Formalization Note** The while loop of Step 3 is this guarded pass iterated enough times (see Subroutine 1.1); once the guard fails, further passes change nothing.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Subroutine 1.1, Step 3, p. 10

import Mathlib

namespace RollingProbeQN.Convex

/-- **One pass of Step 3 of Subroutine 1.1.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Subroutine 1.1, Step 3, p. 10: "While `λ+/λ− > 2^{1/4}`: set `λ = √(λ−λ+)`; if `Ψ̂_k(λ) < σ`,
set `λ− = λ`, otherwise set `λ+ = λ`."

The state is `(λ−, λ+, n)`, with `n` the number of evaluations of `Ψ` so far. A pass performs one
iteration of the while loop if its guard holds and does nothing otherwise.

**Formalization Note.** Reading R8: the while loop is this guarded pass iterated a number of times
that is at least the loop's number of iterations (see `subroutine11`); once the guard fails, further
passes change nothing. -/
noncomputable def bisectPass (Ψ : ℝ → ℝ) (σ : ℝ) (p : ℝ × ℝ × ℕ) : ℝ × ℝ × ℕ :=
  if (2 : ℝ) ^ ((1 : ℝ) / 4) < p.2.1 / p.1 then
    if Ψ (Real.sqrt (p.1 * p.2.1)) < σ then (Real.sqrt (p.1 * p.2.1), p.2.1, p.2.2 + 1)
    else (p.1, Real.sqrt (p.1 * p.2.1), p.2.2 + 1)
  else p

end RollingProbeQN.Convex


