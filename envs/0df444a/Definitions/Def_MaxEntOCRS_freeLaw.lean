-- Prove2me | Definitions.Def_MaxEntOCRS_freeLaw
-- name    : MaxEntOCRS_freeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:33:58.893293+00:00
-- url     : https://prove2.me/theorems/2c784c5c-91e7-4004-ad77-e5b1c2bf2b53
-- title:
--   Law $\nu$ of the free neighbourhood $F \subseteq [k]$
-- statement:
--   Fix distinct vertices $u, v$ of $G$. Draw $M'$ from the monomer–dimer measure of $G' = G - u - v$ and let $F \subseteq [k]$ be the set of indices $i$ for which $y_i$ is uncovered by $M'$. Then $\nu$ is the law of $F$:
--   $$
--   \nu(F) = \Pr_{M'}\big(\{ i : y_i \text{ uncovered by } M'\} = F\big).
--   $$
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_prob
import Definitions.Def_MaxEntOCRS_Covers
import Definitions.Def_MaxEntOCRS_deletedMD
import Definitions.Def_MaxEntOCRS_nbrSet

namespace MaxEntOCRS

open Classical in
/-- The law `ν` of the free neighbourhood `F ⊆ [k]`, the set of neighbours `y_i ∈ N` left
uncovered by a matching `M′` drawn from the monomer–dimer measure of `G′ = G − u − v`
(Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5). -/
noncomputable def freeLaw {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (u v : V) :
    Finset (nbrSet G u v) → ℝ :=
  fun F => prob (deletedMD G t u v)
    (fun M => Finset.univ.filter (fun y : nbrSet G u v => ¬ Covers G M y.1) = F)

end MaxEntOCRS


