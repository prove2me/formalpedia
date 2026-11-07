-- Prove2me | Definitions.Def_MaxEntOCRS_Qloc
-- name    : MaxEntOCRS_Qloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:35.736122+00:00
-- url     : https://prove2.me/theorems/fa310044-8486-475c-b839-3664ecfaf2e2
-- title:
--   Localization quantity $Q = 1 + B$
-- statement:
--   For distinct vertices $u, v$, $Q = 1 + B$ with $B = \sum_i b_i p_i$, where $b_i$ is the aggregated activity between $v$ and $y_i$. By Lemma 3, $\Pr(u \text{ uncovered}) = Q/K$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_freeLaw
import Definitions.Def_MaxEntOCRS_pairWt
import Definitions.Def_MaxEntOCRS_incProb

namespace MaxEntOCRS

/-- `Q = 1 + B`, `B = ∑_i b_i p_i` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5), with `b_i` the activity between `v` and
`y_i`. -/
noncomputable def Qloc {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V) : ℝ :=
  1 + ∑ i : nbrSet G u v, pairWt G t v i.1 * incProb (freeLaw G t u v) i

end MaxEntOCRS


