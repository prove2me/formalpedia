-- Prove2me | Definitions.Def_ScarceIdeas_moment
-- name    : ScarceIdeas_moment
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:49.65631+00:00
-- url     : https://prove2.me/theorems/80f16aad-4b53-4fdf-b0d7-95d7a1f66817
-- title:
--   Posterior moments $m_k(\phi)$, equation (31)
-- statement:
--   The $k$-th moment of the planner's beliefs $h_\phi$ at state $\phi$ is
--
--   $$m_k(\phi)=\int_0^\infty\lambda^k h_\phi(\lambda)\,d\lambda=\frac{\int_0^\infty\lambda^k h_0(\lambda)e^{-\lambda\phi}\,d\lambda}{\int_0^\infty h_0(\lambda')e^{-\lambda'\phi}\,d\lambda'} .$$
--
--   In particular $m_1(\phi)$ is the expected arrival rate. These moments drive the dynamics of the optimal reward.
--
--   **Formalization Note** Defined directly by the quotient (31), with denominator $Z(\phi)$; the posterior density is not a separate object.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.1, (13), p.19; Appendix, (31), p.34

import Mathlib
import Definitions.Def_ScarceIdeas_normalizer

namespace ScarceIdeas

/-- **Moments `m_k(ϕ)` of the social planner's beliefs `h_ϕ`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.1, (13), p.19 ("mk(ϕ) = ∫_0^∞ λ^k hϕ(λ)dλ for k = 1, 2, ...") in the form (31), p.34:

$$m_k(\phi)=\frac{\int_0^\infty \lambda^k h_0(\lambda)e^{-\lambda\phi}\,d\lambda}
{\int_0^\infty h_0(\lambda')e^{-\lambda'\phi}\,d\lambda'} .$$

**Formalization Note** Defined directly by the quotient (31), so the posterior density (12) need
not be a separate object; the denominator is `normalizer h0 ϕ`. The states of the model are
`ϕ ≥ 0`; under Assumption 1 the denominator is then positive. -/
noncomputable def moment (h0 : ℝ → ℝ) (k : ℕ) (ϕ : ℝ) : ℝ :=
  (∫ lam in Set.Ioi 0, lam ^ k * h0 lam * Real.exp (-lam * ϕ)) / normalizer h0 ϕ

end ScarceIdeas


