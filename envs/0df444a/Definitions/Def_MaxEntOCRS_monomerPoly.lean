-- Prove2me | Definitions.Def_MaxEntOCRS_monomerPoly
-- name    : MaxEntOCRS_monomerPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:35.09337+00:00
-- url     : https://prove2.me/theorems/22026076-1d9b-4315-a79d-0418d3609e61
-- title:
--   Monomer polynomial $P_H(z)$
-- statement:
--   For a multigraph $H$ with activities $t \ge 0$, the **monomer polynomial** is
--   $$
--   P_H(z) = \sum_{M \in \mathcal M(H)} \Big(\prod_{e \in M} t_e\Big) \prod_{j \notin V(M)} z_j ,
--   $$
--   a polynomial in one complex variable $z_j$ per vertex, where $V(M)$ is the set of vertices covered by $M$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 4, p.6

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_Covers

namespace MaxEntOCRS

open Classical in
/-- The monomer polynomial `P_H(z) = ∑_{M ∈ M(H)} (∏_{e ∈ M} t_e) ∏_{j ∉ V(M)} z_j` of a
multigraph `H` with activities `t` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §4, p.6). -/
noncomputable def monomerPoly {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (H : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (z : V → ℂ) : ℂ :=
  ∑ M, if EdmondsMatching65.Polyhedron.IsMatching H M then
    (∏ e ∈ M, (t e : ℂ)) * ∏ j ∈ Finset.univ.filter (fun j => ¬ Covers H M j), z j else 0

end MaxEntOCRS


