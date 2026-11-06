-- Prove2me | Definitions.Def_ConstrSOSP_eps0
-- name    : ConstrSOSP_eps0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:05.714186+00:00
-- url     : https://prove2.me/theorems/cb2f5106-d529-4869-ab1e-7531ebbdd87e
-- title:
--   Base accuracy $\epsilon_0=10^{-10}$
-- statement:
--   $\epsilon_0=10^{-10}$, the tolerance of the gradient and curvature criteria.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.4.1, p.32

import Mathlib

namespace ConstrSOSP

/-- **The base accuracy `ϵ₀ = 10⁻¹⁰`** (arXiv:2604.02285, 2 Nov 2026, §5.4.1, p.32: "For
ϵ0 = 10^−10, the following criteria each exclude an interior (ϵ0, ϵ0)-SOSP"). -/
def eps0 : ℚ :=
  1 / 10 ^ 10

end ConstrSOSP


