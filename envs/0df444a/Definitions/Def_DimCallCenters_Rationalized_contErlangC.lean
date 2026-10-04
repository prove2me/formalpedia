-- Prove2me | Definitions.Def_DimCallCenters_Rationalized_contErlangC
-- name    : DimCallCenters_Rationalized_contErlangC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:04:02.953993+00:00
-- url     : https://prove2.me/theorems/742509b6-ff15-412b-a78a-01786913cba6
-- title:
--   Continuous Erlang-C extension $H(M,\alpha)$
-- statement:
--   For real $M$ and $\alpha > 0$ define
--
--   $$H(M,\alpha) = \left\{\alpha\int_0^\infty e^{-\alpha t}\, t\,(1+t)^{M-1}\,dt\right\}^{-1}.$$
--
--   At integer $M = N > \alpha$ this coincides with the Erlang-C formula $\pi(N,\alpha)$, so $H$ extends the probability of waiting to a non-integer number of servers.
--
--   **Formalization Note** $(1+t)^{M-1}$ is the real power; the integrand is integrable on $(0,\infty)$ for every real $M$ and $\alpha > 0$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, definition of H(M, alpha)

import Mathlib

namespace DimCallCenters.Rationalized

/-- The continuous extension of the Erlang-C formula of p. 12:
`H(M, α) = {α ∫_0^∞ e^{-α t} t (1 + t)^{M-1} dt}⁻¹`, with a real exponent `M - 1`. -/
noncomputable def contErlangC (m α : ℝ) : ℝ :=
  (α * ∫ t in Set.Ioi 0, Real.exp (-α * t) * t * (1 + t) ^ (m - 1))⁻¹

end DimCallCenters.Rationalized


