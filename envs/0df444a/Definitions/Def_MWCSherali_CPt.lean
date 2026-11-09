-- Prove2me | Definitions.Def_MWCSherali_CPt
-- name    : MWCSherali_CPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:11.275676+00:00
-- url     : https://prove2.me/theorems/a020eee1-d43e-4602-b71c-f9d67548ce7b
-- title:
--   Names of the special points of the central region
-- statement:
--   The special points of the central region $Z$: its centre $o$, the vertex $v$, the vertices $v_{12},v_{23},v_{34}$ obtained from $v$ by swapping two coordinates, and the facet centres $h_c,h_s,h_t$. Their coordinates are given by `cpt`.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4.4, p.37

import Mathlib

namespace MWCSherali

/-- **Names of the special points of the central region.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4.4, p.37: the centre
`o`, the vertex `v` of `Z`, its coordinate swaps `v₁₂, v₂₃, v₃₄`, and the facet centres
`h_c, h_s, h_t`. Their coordinates are `cpt`. -/
inductive CPt
  | o
  | v
  | v12
  | v23
  | v34
  | hc
  | hs
  | ht
  deriving DecidableEq, Repr

end MWCSherali


