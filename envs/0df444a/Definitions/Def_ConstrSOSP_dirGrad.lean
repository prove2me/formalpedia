-- Prove2me | Definitions.Def_ConstrSOSP_dirGrad
-- name    : ConstrSOSP_dirGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:45.838889+00:00
-- url     : https://prove2.me/theorems/4262f614-ed50-4e64-aa50-6fe928ea0ec1
-- title:
--   Gradient of an arrow
-- statement:
--   "In the formula below they denote the corresponding gradient vectors $(1/2,0)$, $(-1/2,0)$, $(0,-1/2)$, and $(0,1/2)$": Left $\mapsto(1/2,0)$, Right $\mapsto(-1/2,0)$, Up $\mapsto(0,-1/2)$, Down $\mapsto(0,1/2)$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), p.30

import Mathlib
import Definitions.Def_ConstrSOSP_Dir

namespace ConstrSOSP

/-- **The gradient of an arrow** (arXiv:2604.02285, 2 Nov 2026, p.30: "the direction names Left,
Right, Up, and Down describe negative-gradient arrows. In the formula below they denote the
corresponding gradient vectors (1/2, 0), (−1/2, 0), (0, −1/2), and (0, 1/2)"). -/
noncomputable def dirGrad : Dir → Fin 2 → ℝ
  | Dir.left => ![1 / 2, 0]
  | Dir.right => ![-1 / 2, 0]
  | Dir.up => ![0, -1 / 2]
  | Dir.down => ![0, 1 / 2]

end ConstrSOSP


