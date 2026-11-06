-- Prove2me | Definitions.Def_ConstrSOSP_sqrtEpsF
-- name    : ConstrSOSP_sqrtEpsF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:50.800086+00:00
-- url     : https://prove2.me/theorems/1d61a0e5-77e7-48af-a114-d79d2b036366
-- title:
--   Curvature accuracy $\sqrt\epsilon=\epsilon_0/(c_0N^2)$
-- statement:
--   $\sqrt\epsilon=\epsilon_0/(c_0N^2)$, a positive rational whose square is $\epsilon$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), p.55; Corollary 5.6, p.55

import Mathlib
import Definitions.Def_ConstrSOSP_c0
import Definitions.Def_ConstrSOSP_eps0

namespace ConstrSOSP

/-- **The curvature accuracy `√ϵ = ϵ₀/(c₀ N²)`** of the normalized instance (arXiv:2604.02285,
2 Nov 2026, p.55: "any (ϵ0²/(c0² · N⁴), ϵ0/(c0 · N²))-SOSP of f_sc"; Corollary 5.6, p.55), a
positive rational whose square is `epsF N`. -/
def sqrtEpsF (N : ℕ) : ℚ :=
  eps0 / (c0 * (N : ℚ) ^ 2)

end ConstrSOSP


