-- Prove2me | Definitions.Def_MaxEntOCRS_Kloc
-- name    : MaxEntOCRS_Kloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:14.986194+00:00
-- url     : https://prove2.me/theorems/169cec8a-81b8-431a-937b-313ae712f37c
-- title:
--   Localization quantity $K = \mathbb E_\nu D_F$
-- statement:
--   For distinct vertices $u, v$, $K = \mathbb E_\nu D_F = \sum_F \nu(F) D_F$, the expected local partition function under the law $\nu$ of the free neighbourhood. By Lemma 3, $\Pr(u, v \text{ uncovered}) = 1/K$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_freeLaw
import Definitions.Def_MaxEntOCRS_localPF

namespace MaxEntOCRS

/-- `K = E_ν D_F` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5). By Lemma 3, `Pr(u, v uncovered) = 1/K`. -/
noncomputable def Kloc {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V) : ℝ :=
  ∑ F, freeLaw G t u v F * localPF G t u v F

end MaxEntOCRS


