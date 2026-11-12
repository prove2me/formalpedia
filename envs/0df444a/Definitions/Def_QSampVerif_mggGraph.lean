-- Prove2me | Definitions.Def_QSampVerif_mggGraph
-- name    : QSampVerif_mggGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:28:19.59674+00:00
-- url     : https://prove2.me/theorems/a79da64e-c53e-4c19-b1a7-009900b557c4
-- title:
--   The Margulis–Gabber–Galil multigraph $G_{r_G}$ (Definition 3.14)
-- statement:
--   For an integer $r_G\ge1$, $G_{r_G}$ is the undirected degree-eight multigraph on $\mathbb Z_{r_G}^2$ given by the neighbour maps
--
--   $$(x\pm2y,\,y),\quad(x\pm(2y+1),\,y),\quad(x,\,y\pm2x),\quad(x,\,y\pm(2x+1)),\qquad(39)$$
--
--   with arithmetic modulo $r_G$. Each map and its inverse specify opposite endpoints of the same edges; parallel edges and loops are retained.
--
--   **Formalization Note** Each "$-$" map is the inverse of the corresponding "$+$" map, so the edge multiset has exactly one edge $\{v,f(v)\}$ for every vertex $v$ and every forward map $f\in\{(x+2y,y),(x+2y+1,y),(x,y+2x),(x,y+2x+1)\}$. Every vertex then has degree $8$ (a loop counts twice).
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Definition 3.14, (39), p.21 (PDF 22)

import Definitions.Def_QSampVerif_Multigraph

set_option autoImplicit false

namespace QSampVerif

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Definition 3.14 (Margulis–Gabber–Galil graph), (39), p.21 (PDF 22): the multigraph `G_{r_G}` on
`Z²_{r_G}` with neighbour maps `(x ± 2y, y)`, `(x ± (2y+1), y)`, `(x, y ± 2x)`, `(x, y ± (2x+1))`,
arithmetic modulo `r_G ≥ 1` (`NeZero r`); "Each map and its inverse specify opposite endpoints of the same edges;
parallel edges and loops are retained."

**Formalization Note.** Each `−` map is the inverse of the corresponding `+` map, so the edge
multiset has one edge `s(v, f(v))` for every vertex `v` and every forward map
`f ∈ {(x + 2y, y), (x + 2y + 1, y), (x, y + 2x), (x, y + 2x + 1)}`; the `−` maps give the same edges
from the other endpoint. Every vertex has degree 8 (a loop counts twice). -/
def mggGraph (r : ℕ) [NeZero r] : Multigraph (ZMod r × ZMod r) where
  edges := (Finset.univ : Finset (ZMod r × ZMod r)).val.bind fun v =>
    {s(v, (v.1 + 2 * v.2, v.2)), s(v, (v.1 + (2 * v.2 + 1), v.2)),
      s(v, (v.1, v.2 + 2 * v.1)), s(v, (v.1, v.2 + (2 * v.1 + 1)))}

end QSampVerif


