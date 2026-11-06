-- Prove2me | Definitions.Def_ConstrSOSP_colourPhi
-- name    : ConstrSOSP_colourPhi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:36.390593+00:00
-- url     : https://prove2.me/theorems/01a1074a-60f4-438a-a173-96991613533c
-- title:
--   Colour functions $\Phi_B,\Phi_M,\Phi_R,\Phi_G,\Phi_O$
-- statement:
--   For the grid size $N$:
--   $$
--   \Phi_B=10^4N-x-y,\quad \Phi_M=(10^6+1)N+x-y,\quad \Phi_R=10^4(10^4-2)N-x+y,
--   $$
--   $$
--   \Phi_G=10^{15}N+x-y,\quad \Phi_O=10^{16}N-x+y .
--   $$
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.3, pp.24–25

import Mathlib
import Definitions.Def_ConstrSOSP_Colour

namespace ConstrSOSP

/-- **The colour functions `Φ_B, Φ_M, Φ_R, Φ_G, Φ_O`** (arXiv:2604.02285, 2 Nov 2026, §5.3,
pp.24–25), for the grid size `N`:
* `Φ_B(x, y) = 10⁴N − x − y`,
* `Φ_M(x, y) = (10⁶ + 1)N + x − y`,
* `Φ_R(x, y) = 10⁴(10⁴ − 2)N − x + y`,
* `Φ_G(x, y) = 10¹⁵N + x − y`,
* `Φ_O(x, y) = 10¹⁶N − x + y`. -/
def colourPhi (N : ℝ) : Colour → ℝ → ℝ → ℝ
  | Colour.blue, x, y => 10 ^ 4 * N - x - y
  | Colour.black, x, y => (10 ^ 6 + 1) * N + x - y
  | Colour.red, x, y => 10 ^ 4 * (10 ^ 4 - 2) * N - x + y
  | Colour.green, x, y => 10 ^ 15 * N + x - y
  | Colour.orange, x, y => 10 ^ 16 * N - x + y

end ConstrSOSP


