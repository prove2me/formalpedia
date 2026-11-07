-- Prove2me | Definitions.Def_DDNNFNeg_edgeNbhd
-- name    : DDNNFNeg_edgeNbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:08.129482+00:00
-- url     : https://prove2.me/theorems/faed2a32-68ce-4c02-932c-c62603d9bb1a
-- title:
--   Neighbourhood $N(e)$ of an edge
-- statement:
--   For an edge $e = \{u, v\}$ of $G$, the **neighbourhood** $N(e)$ is the set of vertices containing $u$ and $v$ and every neighbour of $u$ or of $v$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.2, p.12

import Mathlib

namespace DDNNFNeg

/-- The neighbourhood `N(e)` of an edge `e = {u, v}` of `G` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.2, p.12): the set of
vertices containing `u` and `v` and every neighbour of `u` or of `v`. -/
def edgeNbhd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (e : Sym2 (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => w ∈ e ∨ ∃ u, u ∈ e ∧ G.Adj u w)

end DDNNFNeg


