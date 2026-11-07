-- Prove2me | Definitions.Def_MaxEntOCRS_Ploc
-- name    : MaxEntOCRS_Ploc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:50.403401+00:00
-- url     : https://prove2.me/theorems/cd87daa0-3f1f-4111-b5f5-13d8157e1891
-- title:
--   Localization quantity $P = 1 + A$
-- statement:
--   For distinct vertices $u, v$, $P = 1 + A$ with $A = \sum_i a_i p_i$, where $a_i$ is the aggregated activity between $u$ and $y_i$ and $p_i$ the probability that $y_i$ is free in $G - u - v$. By Lemma 3, $\Pr(v \text{ uncovered}) = P/K$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_freeLaw
import Definitions.Def_MaxEntOCRS_pairWt
import Definitions.Def_MaxEntOCRS_incProb

namespace MaxEntOCRS

/-- `P = 1 + A`, `A = ∑_i a_i p_i` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5), with `a_i` the activity between `u` and
`y_i`. -/
noncomputable def Ploc {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V) : ℝ :=
  1 + ∑ i : nbrSet G u v, pairWt G t u i.1 * incProb (freeLaw G t u v) i

end MaxEntOCRS


