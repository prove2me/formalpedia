-- Prove2me | Definitions.Def_LL_Task580_mconv
-- name    : LL_Task580_mconv
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-24T17:27:14.749903+00:00
-- url     : https://prove2.me/theorems/87cd3db4-42f6-4ae8-873b-dbdcfe4446d9
-- title:
--   Multiplicative convolution $(f*_M g)(t)=\int_0^\infty f(y)g(t/y)\,dy/y$
-- statement:
--   For real functions $f,g$ and real $t$, $(f*_M g)(t)$ is the Lebesgue integral over $y\in(0,\infty)$ of $f(y)\,g(t/y)/y$, equal to $0$ when the integrand is not integrable.

import Mathlib

namespace LL_Task580

noncomputable section

noncomputable def mconv (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), f y * g (t / y) / y

end

end LL_Task580


