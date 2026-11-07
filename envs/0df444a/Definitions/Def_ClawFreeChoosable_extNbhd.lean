-- Prove2me | Definitions.Def_ClawFreeChoosable_extNbhd
-- name    : ClawFreeChoosable_extNbhd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:46.746133+00:00
-- url     : https://prove2.me/theorems/f1c20d5b-348b-4141-9933-f757643d87b1
-- title:
--   External neighbourhood $N_G(A)$
-- statement:
--   For a set $A$ of vertices of a graph $G$, its **external neighbourhood** is
--   $$N_G(A) = \Big(\bigcup_{a \in A} N_G(a)\Big) \setminus A,$$
--   the set of vertices outside $A$ having a neighbour in $A$.
--
--   For a clique $S$ of simplicial vertices, $Q = N_G(S)$ is the clique through which $S$ attaches to the rest of the graph (Lemma 7.3).
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §7.1 p.9, "external neighborhood"

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **External neighbourhood** (arXiv:2611.01068v1, §7.1 p.9):
`N_G(A) = (⋃_{a ∈ A} N_G(a)) \ A`, the vertices outside `A` with a neighbour in `A`. -/
def extNbhd {V : Type} (G : SimpleGraph V) (A : Set V) : Set V :=
  {v | v ∉ A ∧ ∃ a ∈ A, G.Adj a v}

end ClawFreeChoosable


