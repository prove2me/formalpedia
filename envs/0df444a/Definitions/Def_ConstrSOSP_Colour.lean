-- Prove2me | Definitions.Def_ConstrSOSP_Colour
-- name    : ConstrSOSP_Colour
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:41.353209+00:00
-- url     : https://prove2.me/theorems/b74ee61b-6689-4b5f-bdfd-cc34f18f889b
-- title:
--   Colour value regimes B, M, R, G, O
-- statement:
--   The five colour value regimes of the construction: blue (B), black (M), red (R), green (G) and orange (O), ordered by value $B<M<R<G<O$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §5.3, pp.24–25

import Mathlib

namespace ConstrSOSP

/-- **The colour value regimes** (arXiv:2604.02285, 2 Nov 2026, §5.3, pp.24–25): blue (B), black
(M), red (R), green (G) and orange (O), "ordered according to decreasing value" from orange down
to blue (Figure 6, p.25: "B < M < R < G < O"). -/
inductive Colour where
  | blue
  | black
  | red
  | green
  | orange

end ConstrSOSP


