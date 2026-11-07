-- Prove2me | Definitions.Def_ClawFreeChoosable_IsAnticomplete
-- name    : ClawFreeChoosable_IsAnticomplete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:53.137193+00:00
-- url     : https://prove2.me/theorems/f7833a03-208a-4b51-ad6d-b97223d5ae1e
-- title:
--   Complete, anticomplete and incomplete pairs of vertex sets
-- statement:
--   Let $A, B$ be sets of vertices of a graph $G$ (the paper uses disjoint sets).
--
--   1. $(A, B)$ is a **complete pair** if every vertex of $A$ is adjacent to every vertex of $B$.
--   2. $(A, B)$ is an **anticomplete pair** if no vertex of $A$ is adjacent to a vertex of $B$.
--   3. $(A, B)$ is an **incomplete pair** if it is neither complete nor anticomplete.
--
--   These relations describe how the cliques of the structural decompositions (clique cutsets, fibres of interval-type graphs, the nine cliques of peculiar graphs) are joined.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §7.1 p.9, "complete pair", "anticomplete pair", "incomplete pair"; Definition 11.1 p.24

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Anticomplete pair** (arXiv:2611.01068v1, §7.1 p.9): no edge of `G` joins `A` and `B`. -/
def IsAnticomplete {V : Type} (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/-- **Complete pair** (arXiv:2611.01068v1, §7.1 p.9): every possible edge between `A` and `B` is
present. The paper uses it for disjoint sets only. -/
def IsComplete {V : Type} (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

/-- **Incomplete pair** (arXiv:2611.01068v1, §7.1 p.9, and Definition 11.1 p.24): a pair of
vertex sets that is neither complete nor anticomplete. -/
def IsIncompletePair {V : Type} (G : SimpleGraph V) (A B : Set V) : Prop :=
  ¬ IsComplete G A B ∧ ¬ IsAnticomplete G A B

end ClawFreeChoosable


