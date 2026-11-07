-- Prove2me | Definitions.Def_MaxEntOCRS_Covers
-- name    : MaxEntOCRS_Covers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:14.796875+00:00
-- url     : https://prove2.me/theorems/77c6a0fd-c7ba-4962-8ce2-d3ad8cd4c250
-- title:
--   Covered and uncovered vertices
-- statement:
--   Let $G = (V, E)$ be a finite loopless multigraph and $M \subseteq E$ a set of edges. A vertex $z$ is **covered** by $M$ if some edge of $M$ contains $z$, and **uncovered** (free) otherwise.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace MaxEntOCRS

/-- A vertex `z` is *covered* by a set of edges `M` if some edge of `M` contains it, and
*uncovered (free)* otherwise (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4). -/
def Covers {V E : Type} (G : EdmondsMatching65.Polyhedron.Graph V E) (M : Finset E) (z : V) : Prop :=
  ∃ e ∈ M, z ∈ G.ends e

end MaxEntOCRS


