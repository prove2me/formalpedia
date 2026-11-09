-- Prove2me | Definitions.Def_InflMaxAdapt_edgeCascade
-- name    : InflMaxAdapt_edgeCascade
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:03.877518+00:00
-- url     : https://prove2.me/theorems/b8a9792f-0bda-4e1c-b049-36a34872d8a1
-- title:
--   Cascade in the undirected-edge representation
-- statement:
--   In the undirected-edge representation, the cascade $C(S)$ of a seed set $S$ is the set of vertices connected to $S$ by paths of live edges.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib
import Definitions.Def_InflMaxAdapt_ConnSet

namespace InflMaxAdapt

/-- The cascade `C(S)` in the undirected-edge representation (Sections 1.1 and 2, printed
pp.2, 5 = PDF pp.3, 6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): the vertices connected to `S` by live edges of `E`. -/
noncomputable def edgeCascade {V : Type} [Fintype V] (E : Finset (Sym2 V)) (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => ConnSet E w S

end InflMaxAdapt


