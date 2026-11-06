-- Prove2me | Definitions.Def_ConstrSOSP_epsF
-- name    : ConstrSOSP_epsF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:21.399863+00:00
-- url     : https://prove2.me/theorems/2ffec17f-2ab5-4d7e-9a00-75602f5650f9
-- title:
--   Accuracy $\epsilon=\epsilon_0^2/(c_0^2N^4)$
-- statement:
--   $\epsilon=\epsilon_0^2/(c_0^2N^4)$, the accuracy of the normalized instance, a positive rational.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Corollary 5.6, p.55

import Mathlib
import Definitions.Def_ConstrSOSP_c0
import Definitions.Def_ConstrSOSP_eps0

namespace ConstrSOSP

/-- **The accuracy `ϵ = ϵ₀²/(c₀² N⁴)`** of the normalized instance (arXiv:2604.02285, 2 Nov 2026,
Corollary 5.6, p.55: "and ϵ = ϵ0^2/(c0^2 N^4)"), for the grid size `N`. -/
def epsF (N : ℕ) : ℚ :=
  eps0 ^ 2 / (c0 ^ 2 * (N : ℚ) ^ 4)

end ConstrSOSP


