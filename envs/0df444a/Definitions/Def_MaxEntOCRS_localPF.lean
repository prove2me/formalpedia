-- Prove2me | Definitions.Def_MaxEntOCRS_localPF
-- name    : MaxEntOCRS_localPF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:16.821088+00:00
-- url     : https://prove2.me/theorems/45c9c5b4-c05b-4d79-b18a-64c03dde60ca
-- title:
--   Local partition function $D_F$
-- statement:
--   For $F \subseteq [k]$, the partition function of the local graph on $u$, $v$ and $\{y_i : i \in F\}$ (the edges $uv$, $uy_i$, $vy_i$ with the aggregated activities) is
--   $$
--   D_F = 1 + w + \sum_{i \in F} (a_i + b_i) + \sum_{\substack{i, j \in F \\ i \ne j}} a_i b_j ,
--   $$
--   where the double sum runs over ordered pairs.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_pairWt

namespace MaxEntOCRS

/-- The local partition function
`D_F = 1 + w + ∑_{i ∈ F} (a_i + b_i) + ∑_{i, j ∈ F, i ≠ j} a_i b_j` of the local graph on `u`,
`v` and `{y_i : i ∈ F}` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5). The double sum runs over ordered pairs. -/
noncomputable def localPF {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V)
    (F : Finset (nbrSet G u v)) : ℝ :=
  1 + pairWt G t u v + ∑ i ∈ F, (pairWt G t u i.1 + pairWt G t v i.1) +
    ∑ i ∈ F, ∑ j ∈ F, if i ≠ j then pairWt G t u i.1 * pairWt G t v j.1 else 0

end MaxEntOCRS


