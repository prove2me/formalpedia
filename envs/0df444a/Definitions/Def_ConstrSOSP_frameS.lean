-- Prove2me | Definitions.Def_ConstrSOSP_frameS
-- name    : ConstrSOSP_frameS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:00:49.339198+00:00
-- url     : https://prove2.me/theorems/aacf53b3-5521-4d9c-9019-0b5ea026833c
-- title:
--   Framed side length $S=N+2m$
-- statement:
--   $S=N+2m$, the side of the framed square $[-m,N+m]^2$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, p.55

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_frameM

namespace ConstrSOSP

/-- **The framed side length `S = N + 2m`** (arXiv:2604.02285, 2 Nov 2026, proof of
Corollary 5.6, p.55). -/
def frameS (n : ℕ) : ℕ :=
  gridN n + 2 * frameM n

end ConstrSOSP


