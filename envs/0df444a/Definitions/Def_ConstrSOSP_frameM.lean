-- Prove2me | Definitions.Def_ConstrSOSP_frameM
-- name    : ConstrSOSP_frameM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:22.711284+00:00
-- url     : https://prove2.me/theorems/c52349bf-8d17-4e07-95ee-c92f3573c5c5
-- title:
--   Frame width $m=\lfloor N/8\rfloor$
-- statement:
--   $m=\lfloor N/8\rfloor$, the width of the frame added around $[0,N]^2$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, p.55

import Mathlib
import Definitions.Def_ConstrSOSP_gridN

namespace ConstrSOSP

/-- **The frame width `m = ⌊N/8⌋`** (arXiv:2604.02285, 2 Nov 2026, proof of Corollary 5.6, p.55:
"Put m = ⌊N/8⌋, S = N + 2m, and extend the grid to [−m, N + m]^2"). -/
def frameM (n : ℕ) : ℕ :=
  gridN n / 8

end ConstrSOSP


