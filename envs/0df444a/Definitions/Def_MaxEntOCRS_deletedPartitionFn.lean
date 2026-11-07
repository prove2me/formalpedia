-- Prove2me | Definitions.Def_MaxEntOCRS_deletedPartitionFn
-- name    : MaxEntOCRS_deletedPartitionFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:42.537482+00:00
-- url     : https://prove2.me/theorems/1aa0c4e3-b7a1-4a5c-8cf4-15a53c4427da
-- title:
--   Partition function $Z(G')$ of $G' = G - u - v$
-- statement:
--   For vertices $u, v$ of $G$ with activities $t$, the partition function of $G' = G - u - v$ is
--   $$
--   Z(G') = \sum_{M \in \mathcal M(G),\ u, v \text{ uncovered by } M} \prod_{e \in M} t_e .
--   $$
--
--   **Formalization Note** The matchings of $G - u - v$ are the matchings of $G$ covering neither $u$ nor $v$, with the same weights; no subgraph type is introduced.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_mdWeight
import Definitions.Def_MaxEntOCRS_Covers

namespace MaxEntOCRS

open Classical in
/-- The partition function `Z(G′)` of `G′ = G − u − v` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5).

**Formalization Note** The matchings of `G − u − v` are the matchings of `G` covering neither
`u` nor `v`, with the same weights; `G′` is encoded through them, without a subgraph type. -/
noncomputable def deletedPartitionFn {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V) : ℝ :=
  ∑ M, if ¬ Covers G M u ∧ ¬ Covers G M v then mdWeight G t M else 0

end MaxEntOCRS


