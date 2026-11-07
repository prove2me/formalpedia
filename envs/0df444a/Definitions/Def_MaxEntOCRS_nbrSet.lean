-- Prove2me | Definitions.Def_MaxEntOCRS_nbrSet
-- name    : MaxEntOCRS_nbrSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:24.058182+00:00
-- url     : https://prove2.me/theorems/24184fb5-2cd8-4578-bbb2-a0543e7c3a69
-- title:
--   Neighbourhood $N = \{y_1, \ldots, y_k\}$ of the pair $u, v$
-- statement:
--   For distinct vertices $u, v$ of $G$, $N = \{y_1, \ldots, y_k\}$ is the set of vertices of $G' = G - u - v$ adjacent to $u$ or to $v$: the vertices $y \ne u, v$ joined to $u$ or to $v$ by at least one edge.
--
--   **Formalization Note** The index set $[k]$ is the finite type of elements of $N$, in place of an enumeration $y_1, \ldots, y_k$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace MaxEntOCRS

open Classical in
/-- The set `N = {y₁, …, y_k}` of vertices of `G′ = G − u − v` adjacent to `u` or `v`
(Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5).

**Formalization Note** The index set `[k]` of the paper is the finite subtype of this set,
in place of an enumeration `y₁, …, y_k`. -/
noncomputable def nbrSet {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (u v : V) : Finset V :=
  Finset.univ.filter (fun y => y ≠ u ∧ y ≠ v ∧ ∃ e, G.ends e = s(u, y) ∨ G.ends e = s(v, y))

end MaxEntOCRS


