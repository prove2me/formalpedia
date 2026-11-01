-- Prove2me | Definitions.Def_MarkovSA_polyStep
-- name    : MarkovSA_polyStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:18.957782+00:00
-- url     : https://prove2.me/theorems/8ac5e71a-7933-4d2f-a293-90a58bdf50e9
-- title:
--   Stepsizes $\alpha_k=\alpha/(k+h)^\xi$
-- statement:
--   For $\alpha,h>0$ and $\xi\in[0,1]$, the stepsizes are
--
--   $$
--   \alpha_k=\frac{\alpha}{(k+h)^\xi}.
--   $$
--
--   $\xi=0$ is constant, $\xi=1$ linear and $\xi\in(0,1)$ polynomial.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.1, p.6

import Mathlib

namespace MarkovSA

/-- The stepsizes `α_k = α/(k + h)^ξ` (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.1, p.6), `α, h > 0`, `ξ ∈ [0, 1]`.

**Formalization Note.** `(k + h)^ξ` is `Real.rpow` with the positive base `k + h`; `ξ = 1` gives `α/(k+h)`. -/
noncomputable def polyStep (a h ξ : ℝ) (k : ℕ) : ℝ := a / ((k : ℝ) + h) ^ ξ

end MarkovSA


