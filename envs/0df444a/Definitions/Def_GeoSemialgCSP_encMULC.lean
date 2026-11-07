-- Prove2me | Definitions.Def_GeoSemialgCSP_encMULC
-- name    : GeoSemialgCSP_encMULC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:21.258987+00:00
-- url     : https://prove2.me/theorems/42e0a74e-72ad-43ea-a298-902b7492b248
-- title:
--   Unary encoding of a Unique Games instance
-- statement:
--   A Unique Games instance is encoded over $\{1,\mathrm{sep}\}$: the numbers of left and right vertices and the alphabet size in unary, then for each edge occurrence $(u,v,\pi)$ the numbers $u$, $v$ and the table $\pi(0),\dots,\pi(M-1)$ in unary. The length is polynomial in the size of the instance.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_GeoSemialgCSP_MULC
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace GeoSemialgCSP

/-- **Encoding of a Unique Games instance with parallel edges.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §6, printed p.17
(PDF p.18).

Over the alphabet `{1, sep}` of `OptInapprox.MaxCut.MCSym`: `nV`, `nW`, `M` in unary, then for each
edge occurrence `(u, v, π)` the numbers `u`, `v` and the table `π(0), …, π(M−1)` in unary.

**Formalization Note.** A fixed unary encoding of polynomial length, as for the published
`OptInapprox.MaxCut.encULC`. -/
def encMULC (L : MULC) : List OptInapprox.MaxCut.MCSym :=
  OptInapprox.MaxCut.MCSym.unary L.nV ++ OptInapprox.MaxCut.MCSym.unary L.nW ++
    OptInapprox.MaxCut.MCSym.unary L.M ++
    L.edges.flatMap fun e => OptInapprox.MaxCut.MCSym.unary (e.1 : ℕ) ++
      OptInapprox.MaxCut.MCSym.unary (e.2.1 : ℕ) ++
      (List.finRange L.M).flatMap fun j => OptInapprox.MaxCut.MCSym.unary (e.2.2 j : ℕ)

end GeoSemialgCSP


