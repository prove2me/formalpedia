-- Prove2me | Definitions.Def_MaxEntOCRS_Hloc
-- name    : MaxEntOCRS_Hloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:49.515899+00:00
-- url     : https://prove2.me/theorems/e79d9689-765c-400c-87af-b394883e64f4
-- title:
--   Localization quantity $H_i = \mathbb E_\nu[X_i D_{F\setminus\{i\}}]$
-- statement:
--   For distinct vertices $u, v$ and a neighbour index $i$,
--   $$
--   H_i = \mathbb E_\nu\big[X_i D_{F \setminus \{i\}}\big] = \sum_{F \ni i} \nu(F) D_{F\setminus\{i\}} .
--   $$
--   By Lemma 3, $\Pr(y_i \text{ uncovered}) = H_i/K$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_freeLaw
import Definitions.Def_MaxEntOCRS_localPF

namespace MaxEntOCRS

/-- `H_i = E_ν[X_i D_{F∖{i}}]` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5). -/
noncomputable def Hloc {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V) (i : nbrSet G u v) : ℝ :=
  ∑ F, freeLaw G t u v F * (if i ∈ F then localPF G t u v (F.erase i) else 0)

end MaxEntOCRS


