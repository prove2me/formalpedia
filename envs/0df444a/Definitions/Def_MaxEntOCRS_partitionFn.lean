-- Prove2me | Definitions.Def_MaxEntOCRS_partitionFn
-- name    : MaxEntOCRS_partitionFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:45.886199+00:00
-- url     : https://prove2.me/theorems/c0c14029-8208-4fb1-aa92-66a66d8e43a0
-- title:
--   Monomer–dimer partition function $Z(G)$
-- statement:
--   The **partition function** of a finite loopless multigraph $G$ with activities $t$ is
--   $$
--   Z(G) = \sum_{M \in \mathcal M(G)} \prod_{e \in M} t_e .
--   $$
--   For $t \ge 0$ it is at least $1$ (the empty matching).
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_mdWeight

namespace MaxEntOCRS

/-- The monomer–dimer partition function `Z(G) = ∑_{M ∈ M(G)} ∏_{e ∈ M} t_e` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4). -/
noncomputable def partitionFn {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) : ℝ :=
  ∑ M, mdWeight G t M

end MaxEntOCRS


