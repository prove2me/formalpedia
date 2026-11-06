-- Prove2me | Definitions.Def_ConstrSOSP_Dir
-- name    : ConstrSOSP_Dir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:44.044636+00:00
-- url     : https://prove2.me/theorems/227f13ad-ce9e-4a8a-a93d-ce85126159ab
-- title:
--   Arrows Left, Right, Up, Down
-- statement:
--   The four negative-gradient arrows Left, Right, Up and Down of the construction.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.3, pp.25, 30

import Mathlib

namespace ConstrSOSP

/-- **The four arrows of the construction** (arXiv:2604.02285, 2 Nov 2026, §5.3, p.25 and p.30):
"the direction names Left, Right, Up, and Down describe negative-gradient arrows". The gradient
each arrow stands for is `dirGrad`. -/
inductive Dir where
  | left
  | right
  | up
  | down

end ConstrSOSP


