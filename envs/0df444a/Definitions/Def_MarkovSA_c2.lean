-- Prove2me | Definitions.Def_MarkovSA_c2
-- name    : MarkovSA_c2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:16.615626+00:00
-- url     : https://prove2.me/theorems/f8b5b405-5fca-4f78-81e4-59ba414316ea
-- title:
--   $c_2=(A\|x^*\|_c+B)^2$
-- statement:
--   $$
--   c_2=\big(A\|x^*\|_c+B\big)^2,
--   $$
--
--   the constant that represents the noise level at $x^*$ in the bounds of Theorem 2.1.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.2, p.6

import Mathlib

namespace MarkovSA

/-- `c₂ = (A‖x*‖_c + B)²` (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.2, p.6). -/
noncomputable def c2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (xstar : E) (A B : ℝ) : ℝ := (A * ‖xstar‖ + B) ^ 2

end MarkovSA


