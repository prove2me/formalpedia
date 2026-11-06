-- Prove2me | Definitions.Def_ConstrSOSP_c0
-- name    : ConstrSOSP_c0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:47.896097+00:00
-- url     : https://prove2.me/theorems/6450013e-fb04-4503-8889-f47f6e9cee89
-- title:
--   Normalization constant $c_0=2^{76}$
-- statement:
--   $c_0=2^{76}$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Corollary 5.6, p.55

import Mathlib

namespace ConstrSOSP

/-- **The normalization constant `c₀ = 2⁷⁶`** (arXiv:2604.02285, 2 Nov 2026, Corollary 5.6, p.55:
"where c0 = 2^76"; p.54: "we divide by a factor of c0 · N^4, where c0 = 2^76"). -/
def c0 : ℚ :=
  2 ^ 76

end ConstrSOSP


