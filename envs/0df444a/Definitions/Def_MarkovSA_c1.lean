-- Prove2me | Definitions.Def_MarkovSA_c1
-- name    : MarkovSA_c1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:16.077493+00:00
-- url     : https://prove2.me/theorems/32cb2ab2-4cb8-4602-a2e2-64b6a6d5e044
-- title:
--   $c_1=(\|x_0-x^*\|_c+\|x_0\|_c+B/A)^2$
-- statement:
--   $$
--   c_1=\big(\|x_0-x^*\|_c+\|x_0\|_c+B/A\big)^2,
--   $$
--
--   the constant that carries the initial error into the bounds of Theorem 2.1.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.2, p.6

import Mathlib

namespace MarkovSA

/-- `c₁ = (‖x₀ − x*‖_c + ‖x₀‖_c + B/A)²` (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.2, p.6). -/
noncomputable def c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (x₀ xstar : E) (A B : ℝ) : ℝ := (‖x₀ - xstar‖ + ‖x₀‖ + B / A) ^ 2

end MarkovSA


