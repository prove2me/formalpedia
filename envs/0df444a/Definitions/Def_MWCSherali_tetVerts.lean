-- Prove2me | Definitions.Def_MWCSherali_tetVerts
-- name    : MWCSherali_tetVerts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:33.944429+00:00
-- url     : https://prove2.me/theorems/44c468eb-6698-4da3-818a-e89300c18a29
-- title:
--   The six representative tetrahedra of the central region
-- statement:
--   The central region is triangulated into 72 tetrahedra by joining the centre $o$ to triangles of its boundary facets. Up to coordinate permutations there are six of them (Table 5):
--
--   $$\operatorname{conv}(o,h_c,v,v_{23}),\ \operatorname{conv}(o,h_c,v,v_{34}),\ \operatorname{conv}(o,h_s,v,v_{12}),\ \operatorname{conv}(o,h_s,v,v_{23}),\ \operatorname{conv}(o,h_t,v,v_{12}),\ \operatorname{conv}(o,h_t,v,v_{34}),$$
--
--   listed in this order, each by its four vertices.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Table 5, p.38; §4.4, p.37

import Mathlib
import Definitions.Def_MWCSherali_CPt

namespace MWCSherali

/-- **The six representative tetrahedra of the central region.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Table 5, p.38:
`conv(o, h_c, v, v₂₃)`, `conv(o, h_c, v, v₃₄)`, `conv(o, h_s, v, v₁₂)`, `conv(o, h_s, v, v₂₃)`,
`conv(o, h_t, v, v₁₂)`, `conv(o, h_t, v, v₃₄)`, in this order (`r = 0, …, 5`), each as its list of
four vertex names. All 72 tetrahedra of the triangulation of `Z` (p.37) are images of these six
under coordinate permutations. -/
def tetVerts : Fin 6 → Fin 4 → CPt :=
  ![![.o, .hc, .v, .v23], ![.o, .hc, .v, .v34], ![.o, .hs, .v, .v12],
    ![.o, .hs, .v, .v23], ![.o, .ht, .v, .v12], ![.o, .ht, .v, .v34]]

end MWCSherali


